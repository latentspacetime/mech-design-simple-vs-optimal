#!/usr/bin/env python3
"""Frozen post-freeze metadata delta verifier for arXiv release tarballs.

Compatible with Python 3.9 through 3.15+.
Enforces the sole permitted post-freeze change (updating literal fields in paper/metadata.json):
  1. Authenticates the frozen audited baseline tarball AND every audited non-metadata
     paper member directly against the frozen SHA256SUMS.txt manifest (never trusting an
     unmanifested .frozen_audited copy or an unauthenticated live tarball).
  2. Runs frozen scripts/render_metadata.py to regenerate paper/metadata.tex.
  3. Rebuilds the deterministic arXiv tarball from paper/ using gzip.GzipFile(mtime=0).
  4. Unpacks BOTH the authenticated frozen tarball and the newly rebuilt tarball in /tmp,
     asserting that EVERY non-metadata member matches byte-for-byte against BOTH the
     authenticated frozen tarball AND SHA256SUMS.txt, and that archived metadata.tex matches
     freshly generated paper/metadata.tex.
  5. Compiles the rebuilt tarball with TeX Live pdflatex in /tmp (3 passes), renders
     preview PNGs via Ghostscript if available, and prints the updated release SHA-256
     alongside the unchanged audited mathematical-content digest.
"""
from __future__ import annotations

import gzip
import hashlib
import importlib.util
import io
import json
import shutil
import subprocess
import sys
import tarfile
import tempfile
from pathlib import Path

TARBALL_SPECS = {
    "tsp": ("arxiv_tsp.tar.gz", "paper_tsp.tex"),
    "mech": ("arxiv_mech_design.tar.gz", "paper_mech_design.tex"),
}


def load_renderer(renderer_path: Path, expected_sha: str | None = None):
    if not renderer_path.is_file():
        raise SystemExit(f"REJECT: missing metadata renderer at {renderer_path}")
    if expected_sha is not None:
        actual_sha = sha256_file(renderer_path)
        if actual_sha != expected_sha:
            raise SystemExit(
                f"REJECT: scripts/render_metadata.py digest mismatch! "
                f"expected={expected_sha} actual={actual_sha}"
            )
    spec = importlib.util.spec_from_file_location("_authenticated_render_metadata", str(renderer_path))
    if spec is None or spec.loader is None:
        raise SystemExit(f"REJECT: failed to load renderer spec from {renderer_path}")
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod.render_metadata


def sha256_bytes(b: bytes) -> str:
    return hashlib.sha256(b).hexdigest()


def sha256_file(p: Path) -> str:
    return sha256_bytes(p.read_bytes())


def detect_bundle(repo_root: Path) -> tuple[str, str]:
    if (repo_root / "paper" / "paper_tsp.tex").is_file():
        return TARBALL_SPECS["tsp"]
    if (repo_root / "paper" / "paper_mech_design.tex").is_file():
        return TARBALL_SPECS["mech"]
    raise SystemExit(f"REJECT: cannot detect bundle main .tex in {repo_root / 'paper'}")


def load_manifest(manifest_path: Path) -> dict[str, str]:
    if not manifest_path.is_file():
        raise SystemExit(f"REJECT: frozen manifest not found at {manifest_path}")
    out: dict[str, str] = {}
    for line in manifest_path.read_text(encoding="utf-8").splitlines():
        line = line.strip()
        if not line:
            continue
        parts = line.split(None, 1)
        if len(parts) != 2:
            raise SystemExit(f"REJECT: malformed SHA256SUMS line: {line!r}")
        digest, rel = parts[0].strip(), parts[1].strip()
        if rel.startswith("*"):
            rel = rel[1:]
        if rel.startswith("./"):
            rel = rel[2:]
        out[rel] = digest
    return out


def build_deterministic_tarball(paper_dir: Path, main_tex: str, dest_tar: Path) -> None:
    members = sorted(
        [
            p
            for p in paper_dir.iterdir()
            if p.is_file() and p.name in (main_tex, "proof_body.tex", "metadata.tex", "00README.json", "00README.XXX")
        ],
        key=lambda p: p.name,
    )
    names = [m.name for m in members]
    if main_tex not in names or "proof_body.tex" not in names or "metadata.tex" not in names:
        raise SystemExit(f"REJECT: required TeX files missing in {paper_dir} (found {names})")

    with open(dest_tar, "wb") as raw_f:
        with gzip.GzipFile(filename="", mode="wb", fileobj=raw_f, compresslevel=9, mtime=0) as gz:
            with tarfile.open(fileobj=gz, mode="w", format=tarfile.GNU_FORMAT) as tf:
                for m in members:
                    info = tarfile.TarInfo(name=m.name)
                    data = m.read_bytes()
                    info.size = len(data)
                    info.mtime = 0
                    info.mode = 0o644
                    info.uid = 0
                    info.gid = 0
                    info.uname = ""
                    info.gname = ""
                    tf.addfile(info, io.BytesIO(data))


def unpack_and_hash(tar_path: Path, dest_dir: Path) -> dict[str, str]:
    dest_resolved = dest_dir.resolve()
    with tarfile.open(tar_path, "r:gz") as tf:
        for member in tf.getmembers():
            if not member.isfile():
                raise SystemExit(f"REJECT: non-regular tar member {member.name!r} in {tar_path}")
            target = (dest_resolved / member.name).resolve()
            if target.parent != dest_resolved or "/" in member.name or "\\" in member.name or member.name in (".", ".."):
                raise SystemExit(f"REJECT: unsafe tar member path {member.name!r} in {tar_path}")
        if sys.version_info >= (3, 12):
            tf.extractall(dest_dir, filter="data")
        else:
            tf.extractall(dest_dir)
    hashes = {}
    for p in sorted(dest_dir.rglob("*")):
        if p.is_file():
            hashes[str(p.relative_to(dest_dir))] = sha256_file(p)
    return hashes


def find_pdflatex() -> str:
    for candidate in (
        shutil.which("pdflatex"),
        str(Path.home() / "Library/TinyTeX/bin/universal-darwin/pdflatex"),
        str(Path.home() / ".local/bin/pdflatex"),
        "/Library/TeX/texbin/pdflatex",
    ):
        if candidate and Path(candidate).is_file():
            return candidate
    raise SystemExit("REJECT: TeX Live pdflatex not found on host.")


def compile_pdflatex(work_dir: Path, main_tex: str) -> tuple[str, Path]:
    pdflatex = find_pdflatex()
    ver = subprocess.run([pdflatex, "--version"], capture_output=True, text=True, check=True).stdout.splitlines()[0]
    for pass_idx in range(1, 4):
        p = subprocess.run(
            [pdflatex, "-interaction=nonstopmode", "-halt-on-error", main_tex],
            cwd=str(work_dir),
            capture_output=True,
            text=True,
        )
        if p.returncode != 0:
            raise SystemExit(f"REJECT: pdflatex pass {pass_idx} failed:\n{p.stdout[-2000:]}\n{p.stderr}")
    log_path = work_dir / (Path(main_tex).stem + ".log")
    log_text = log_path.read_text(encoding="utf-8", errors="replace")
    for bad in ("Undefined control sequence", "LaTeX Warning: Reference", "LaTeX Warning: Citation", "Rerun to get"):
        if bad in log_text:
            raise SystemExit(f"REJECT: unresolved TeX Live warning/error ({bad!r}) in {log_path}")
    return ver, work_dir / (Path(main_tex).stem + ".pdf")


def main() -> None:
    repo_root = Path(__file__).resolve().parent.parent
    paper_dir = repo_root / "paper"
    renderer_path = repo_root / "scripts" / "render_metadata.py"
    tar_name, main_tex = detect_bundle(repo_root)
    live_tar = repo_root / tar_name
    init_build = "--init-build" in sys.argv

    if init_build:
        render_metadata = load_renderer(renderer_path, expected_sha=None)
        meta_tex = render_metadata(paper_dir)
        with tempfile.TemporaryDirectory(prefix="release_init_") as td:
            tdir = Path(td)
            rebuilt_tar = tdir / tar_name
            build_deterministic_tarball(paper_dir, main_tex, rebuilt_tar)
            new_dir = tdir / "new_unpacked"
            new_dir.mkdir()
            new_hashes = unpack_and_hash(rebuilt_tar, new_dir)
            tex_ver, pdf_path = compile_pdflatex(new_dir, main_tex)
            shutil.copy2(rebuilt_tar, live_tar)
            shutil.copy2(pdf_path, paper_dir / pdf_path.name)
            print(json.dumps({
                "status": "INIT_BUILD_OK",
                "tex_engine": tex_ver,
                "tarball": str(live_tar),
                "tarball_sha256": sha256_file(live_tar),
                "members": new_hashes,
            }, indent=2))
            return

    # 1. Load frozen SHA256SUMS.txt and authenticate scripts/render_metadata.py BEFORE importing it
    manifest = load_manifest(repo_root / "SHA256SUMS.txt")
    if "scripts/render_metadata.py" not in manifest:
        raise SystemExit("REJECT: scripts/render_metadata.py missing from frozen SHA256SUMS.txt")
    render_metadata = load_renderer(renderer_path, expected_sha=manifest["scripts/render_metadata.py"])

    # 2. Regenerate metadata.tex from metadata.json via authenticated frozen renderer
    meta_tex = render_metadata(paper_dir)
    fresh_meta_hash = sha256_file(meta_tex)

    # 3. Authenticate baseline tarball against frozen SHA256SUMS.txt
    if tar_name not in manifest:
        raise SystemExit(f"REJECT: {tar_name} missing from frozen SHA256SUMS.txt")
    expected_tar_sha = manifest[tar_name]

    frozen_backup = paper_dir / f"{tar_name}.frozen_audited"
    frozen_tar: Path | None = None
    for cand in (frozen_backup, live_tar):
        if cand.is_file() and sha256_file(cand) == expected_tar_sha:
            frozen_tar = cand
            break
    if frozen_tar is None:
        raise SystemExit(
            f"REJECT: neither {frozen_backup} nor {live_tar} matches frozen SHA256SUMS.txt digest {expected_tar_sha}."
        )

    # 3. Rebuild tarball into temp first, verify byte-for-byte delta against authenticated baseline + manifest
    with tempfile.TemporaryDirectory(prefix="release_delta_") as td:
        tdir = Path(td)
        rebuilt_tar = tdir / tar_name
        build_deterministic_tarball(paper_dir, main_tex, rebuilt_tar)

        old_dir = tdir / "old_unpacked"
        new_dir = tdir / "new_unpacked"
        old_dir.mkdir()
        new_dir.mkdir()
        old_hashes = unpack_and_hash(frozen_tar, old_dir)
        new_hashes = unpack_and_hash(rebuilt_tar, new_dir)

        if set(old_hashes.keys()) != set(new_hashes.keys()):
            raise SystemExit(
                f"REJECT: tarball member set changed! old={sorted(old_hashes)} new={sorted(new_hashes)}"
            )
        non_meta_digests = {}
        for name in sorted(new_hashes.keys()):
            if name == "metadata.tex":
                if new_hashes[name] != fresh_meta_hash:
                    raise SystemExit("REJECT: archived metadata.tex does not match freshly rendered paper/metadata.tex")
            else:
                manifest_key = f"paper/{name}"
                if manifest_key not in manifest:
                    raise SystemExit(f"REJECT: non-metadata member '{manifest_key}' missing from SHA256SUMS.txt")
                if old_hashes[name] != manifest[manifest_key]:
                    raise SystemExit(
                        f"REJECT: baseline tarball member '{name}' does not match SHA256SUMS.txt ({manifest[manifest_key]})"
                    )
                if old_hashes[name] != new_hashes[name]:
                    raise SystemExit(
                        f"REJECT: audited non-metadata member '{name}' changed! "
                        f"frozen={old_hashes[name]} rebuilt={new_hashes[name]}"
                    )
                non_meta_digests[name] = new_hashes[name]

        # 4. Compile rebuilt tarball cleanly in /tmp with TeX Live pdflatex
        tex_ver, pdf_path = compile_pdflatex(new_dir, main_tex)

        # 5. Render preview PNGs if gs is available
        preview_dir = tdir / "previews"
        preview_dir.mkdir()
        gs = shutil.which("gs")
        preview_pages = 0
        if gs:
            subprocess.run(
                [gs, "-q", "-dNOPAUSE", "-dBATCH", "-sDEVICE=png16m", "-r120",
                 f"-sOutputFile={preview_dir}/page_%02d.png", str(pdf_path)],
                check=True,
            )
            preview_pages = len(list(preview_dir.glob("page_*.png")))

        # Preserve authenticated frozen baseline copy before replacing live_tar (overwriting any stale backup)
        if sha256_file(rebuilt_tar) != expected_tar_sha:
            if not (frozen_backup.is_file() and sha256_file(frozen_backup) == expected_tar_sha):
                shutil.copy2(frozen_tar, frozen_backup)
        shutil.copy2(rebuilt_tar, live_tar)
        shutil.copy2(pdf_path, paper_dir / pdf_path.name)

        math_digest = sha256_bytes(json.dumps(non_meta_digests, sort_keys=True).encode("utf-8"))
        report = {
            "status": "DELTA_VERIFIED_OK",
            "tex_engine": tex_ver,
            "tarball": str(live_tar),
            "authenticated_baseline_sha256": expected_tar_sha,
            "updated_tarball_sha256": sha256_file(live_tar),
            "audited_math_content_sha256": math_digest,
            "metadata_tex_sha256": fresh_meta_hash,
            "non_metadata_members": non_meta_digests,
            "rendered_preview_pages": preview_pages,
        }
        print(json.dumps(report, indent=2))


if __name__ == "__main__":
    main()

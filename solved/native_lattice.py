"""Compiled accelerator for interval characteristic polynomials of large lattices.

``interval_characteristic(lattice)`` returns exactly the same data as
``solved.matroid_lattice.interval_characteristic``; the test suite compares the two on
every lattice it constructs. The C source is ``native/lattice_intervals.c``. It is compiled
on first use into ``build/`` with a content hash in the file name, so an edited source is
never paired with a stale binary. The program aborts on int64 overflow instead of wrapping.
"""

import hashlib
import shutil
import struct
import subprocess
import sys
from array import array
from pathlib import Path

from .intpoly import trim

ROOT = Path(__file__).resolve().parent.parent
SOURCE = ROOT / "native" / "lattice_intervals.c"
BUILD = ROOT / "build"
FLAGS = ("-O2", "-std=c11", "-Wall", "-Wextra", "-Werror")


class NativeUnavailable(RuntimeError):
    """No C compiler is available to build the accelerator."""


def executable():
    source = SOURCE.read_bytes()
    digest = hashlib.sha256(source + " ".join(FLAGS).encode()).hexdigest()[:16]
    target = BUILD / f"lattice_intervals-{digest}"
    if target.exists():
        return target
    compiler = shutil.which("cc") or shutil.which("gcc")
    if compiler is None:
        raise NativeUnavailable("no C compiler found on PATH")
    BUILD.mkdir(exist_ok=True)
    partial = target.with_suffix(".partial")
    subprocess.run([compiler, *FLAGS, "-o", str(partial), str(SOURCE)], check=True)
    partial.replace(target)
    return target


def _int64_array(values):
    a = array("q", values)
    if sys.byteorder != "little":
        a.byteswap()
    return a


def _read_int64(data, offset, count):
    a = array("q")
    a.frombytes(data[offset : offset + 8 * count])
    if sys.byteorder != "little":
        a.byteswap()
    if len(a) != count:
        raise ArithmeticError("native interval computation returned truncated output")
    return a


def _encode(lattice):
    words = max(1, (lattice.size + 63) // 64)
    header = struct.pack("<qq", len(lattice), words)
    masks = b"".join(flat.to_bytes(8 * words, "little") for flat in lattice.flats)
    return header + _int64_array(lattice.ranks).tobytes() + masks


def interval_characteristic(lattice):
    """List over flats i of dicts j -> chi_[F_i, F_j] coefficient tuple (exact)."""
    result = subprocess.run(
        [str(executable())], input=_encode(lattice), capture_output=True, check=False
    )
    if result.returncode != 0:
        message = result.stderr.decode(errors="replace").strip()
        raise ArithmeticError(f"native interval computation failed: {message}")
    data = result.stdout
    total, width = struct.unpack_from("<qq", data, 0)
    n = len(lattice)
    offset = 16
    offsets = _read_int64(data, offset, n + 1)
    offset += 8 * (n + 1)
    cols = _read_int64(data, offset, total)
    offset += 8 * total
    coeffs = _read_int64(data, offset, total * width)
    if offset + 8 * total * width != len(data) or offsets[-1] != total:
        raise ArithmeticError("native interval computation returned malformed output")
    out = []
    for i in range(n):
        a, b = offsets[i], offsets[i + 1]
        row = {}
        for pair in range(a, b):
            row[cols[pair]] = trim(coeffs[pair * width : (pair + 1) * width].tolist())
        out.append(row)
    return out

# From-source reverification

Independent reverification of the completed development, run on 25 August
2026 on a machine that had never seen this project. Nothing is trusted
here from a binary release, a community cache, or the development laptop.

Target commit `ca586907d97cbbcedc43ba4f5379caf0f3b9d050`, mathlib pinned
at `a3a10db0e9d66acbebf76c5e6a135066525ac900`, Lean `v4.27.0`.

## What was run, twice

Two full legs, one under a Lean toolchain compiled from source with gcc,
the other with clang. Each leg:

1. compiled the Lean toolchain from source;
2. built mathlib and the development **with no cache**;
3. ran the project's own gates — the closure scan, the axiom sweep, and a
   direct `#print axioms` on both forms of the theorem;
4. replayed the entire `Kwon1002` environment through `lean4checker`, an
   independently written checker, from the `.olean` files;
5. recorded sha256 digests of all 131 `Kwon1002` oleans.

## Result

Both legs passed every stage. In each:

- `ProofComplete.erdos1002Conclusion` and `erdos1002Official` depend on
  exactly `propext`, `Classical.choice`, `Quot.sound`;
- the closure scan reports an **empty sorry-leaf set** for the main
  theorem;
- the axiom sweep reports `NONSTANDARD=0` over the whole namespace;
- `lean4checker` replayed the environment without objection.

And across the two legs, **all 131 oleans are byte-identical**, verified
both on the machine and again after download.

## Timings

| | gcc | clang |
|---|---|---|
| toolchain from source | 12 min | 13 min |
| mathlib + development, no cache | 60 min | 60 min |
| gates | 40 min | 39 min |
| lean4checker replay | 3 min | 3 min |

Roughly two hours per leg on 256 cores.

## Reading these files

`MANIFEST.txt` is the run log. Per-leg logs are prefixed `gcc_` and
`clang_`: `closure.log` and `sweep.log` are the project's own gates,
`axioms.log` the direct axiom print, `l4c_replay.log` the independent
checker, and `olean_digests.txt` the digests that were compared.

The script that produced all of this is `pods/pod_verify_1002.sh` in the
audit repository; it is parameterized by compiler and re-runnable.

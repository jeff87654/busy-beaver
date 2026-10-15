# Pinned arithmetic dependency closure

Unmodified source files from the **Coq Library of Undecidability Proofs**:
https://github.com/uds-psl/coq-library-undecidability, commit
`70dfc56f33a6e4835281044e68aa68279989047e` (Coq 8.20).

License: Mozilla Public License 2.0; the upstream `LICENSE` is included.
All source headers and notices are retained verbatim. The dependency closure
of `theories/FOL/Arithmetics/PA.v` consists of 37 `.v` files. The upstream
directory layout and the logical root `Undecidability` are retained.

The four `FOL/Arithmetics` files were retrieved from the pinned commit through
the GitHub connector. The other files and license were copied from the existing
`ZF/stdzf_r3/vendor/undecidability` subset in this repository. Every copied and
retrieved file's Git blob SHA1 was checked against the pinned upstream Git tree.
`MANIFEST.json` records both upstream Git blob SHA1 and local SHA256 for every
vendored file, including `LICENSE`. The arithmetic files are not adaptations of
Jeff's `m254` work.

Compile library sources with the upstream option
`-set "Default Proof Using = Type"`. `../../check_paeq.py --source-only` checks
all manifest source hashes, coverage of the endpoint's dependency closure,
and the number of requested assumption reports. The integrated manifest may
also include signature modules used by the compact calculus. Native checking
uses the common `PA/m238/check.py` after integration.

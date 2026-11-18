busycoq (https://github.com/meithecatte/busycoq) at commit bd2e36f -- only
the seven verify/ files needed by BB73 are included; clone the repository for
the full history.
Build: cd verify && for f in LibTactics Helper TM Compute Flip Permute Individual; do coqc -Q . BusyCoq $f.v; done

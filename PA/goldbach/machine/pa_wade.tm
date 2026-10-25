#! start 0.boot.A
# Based on the NQL register machine:
# <https://github.com/sorear/metamath-turing-machines>
#
# States that begin with a digit are the states for the framework of the
# register machine implemented in a turing machine. States that don't begin
# with a digit are the decision tree states from the subroutines and main().
#
# 0. boot
#
0.boot.A 0 1 R 0.boot.B
0.boot.A 1 0 L 0.boot.C
0.boot.B 0 0 R 0.boot.C
0.boot.B 1 0 R 0.boot.B
0.boot.C 0 1 L 0.boot.D
0.boot.C 1 0 R 0.boot.E
0.boot.D 0 0 L 0.boot.E
0.boot.D 1 0 L 6.continue.4
0.boot.E 0 1 L 0.boot.A
0.boot.E 1 0 L 0.boot.B
#
# At the end of boot the tape looks like:
# 100 1000^4 <3.continue.4 01^132 011 01^68
#
# 1. 2. Low-level register operations:
#
# SEL - Shift which register is selected:
#
# 1 [IP] 1.sel> [ZEROS] [REG BLOCK 1] 0 [REG] 00 [REG BLOCK 2]
# ->
# 5.root> 1 [break.0(IP)] [ZEROS] [REG BLOCK 1] 00 [REG] 0 [REG BLOCK 2]
#
# where IP          is the run length limited in 0s instruction pointer,
#       ZEROS       is a run of at least 3 0s,
#       REG BLOCK 1 starts and ends with 1s and has no run of more than one 0,
#       REG BLOCK 2 can have registers or can be empty.
#
# If 00 does not appear in the register file it is conceptually after the last register.
#
# 00 selects the register that appears after it.
#
# INC - Increment selected register.
#
# 1 [IP] 1.inc> [ZEROS] [REG BLOCK 1] 00 [REG] 0 [REG BLOCK 2]
# ->
# 5.root> 1 [break.0(IP)] [ZEROS] [REG BLOCK 1] 0 [inc(REG)] 0 [REG BLOCK 2]
#
# where IP          is the run length limited in 0s instruction pointer,
#       ZEROS       is a run of at least 3 0s,
#       REG BLOCK 1 starts and ends with 1s and has no run of more than one 0,
#       REG BLOCK 2 can have registers or can be empty.
#
# DECNZ - Decrement selected register if not zero.
#          Break an extra layer if it was 0.
#
# 1 [IP] 1.decnz> [ZEROS] [REG BLOCK 1] 00 [REG] 0 [REG BLOCK 2]
# ->
# 5.root> 1 [break.0(IP)] [ZEROS] 0 [REG BLOCK 1] 0 [dec(REG)] 0 [REG BLOCK 2] 0
#
# where IP          is the run length limited in 0s instruction pointer,
#       ZEROS       is a run of at least 2 0s,
#       REG BLOCK 1 starts and ends with 1s and has no runs of more than one 0,
#       REG         is a run of at least two 1s,
#       REG BLOCK 2 is either empty or starts and ends with 1s and has no run of
#                   more than one 0.
#
# or
#
# 1 [IP] 1.decnz> [ZEROS] [REG BLOCK 1] 0010 [REG BLOCK 2]
# ->
# 5.root> 1 [break.1(IP)] [ZEROS] 0 [REG BLOCK 1] 010 [REG BLOCK 2]
#
# where IP          is the run length limited in 0s instruction pointer,
#       ZEROS       is a run of at least 2 0s,
#       REG BLOCK 1 starts and ends with 1s and has no runs of more than one 0,
#       REG BLOCK 2 is either empty or starts and ends with 1s and has no run of
#                   more than one 0.
#
# Both variants of DECNZ shift [REG BLOCK 1] over to the right one cell,
# thus providing more room for the IP. This is useful as the
# bootstrap does not leave enough room for the longest IP used by the larger
# machines.
#
# For all register operations, when going out to the regiser file a 1 is
# written to the tape after the IP so the end of the IP can be identified
# when returning back from the register file.
#
# DECNZ is implemented by:
#
# 1 [IP] 1.decnz> 0 [>0 0s] [REG BLOCK 1] 00 [REG] 0 [REG BLOCK 2]
# 1 [IP] 1 [>0 0s] 0 [updated REGS] 0 <1.ret1
# 5.root> 1 [break.0(IP)] 0 [>0 0s] 0 [updated REGS]
#
# or
#
# 1 [IP] 1.decnz> 0 [>0 0s] [REG BLOCK 1] 0 010 [REG BLOCK 2]
# 1 [IP] 1 [>0 0s] 0 [REG BLOCK 1] 0 <1.ret2 10 [REG BLOCK 2]
# 5.root> 1 [break.2(IP)] 0 [>0 0s] 0 [REG BLOCK 1] 010 [REG BLOCK 2]
#
# 1 [IP] 1.decnz> 0 [>0 0s]
# 1 [IP] 1 1.decnz.b> [>0 0s]
1.decnz 0 1 R 1.decnz.b
# with a 1 on the tape 1.decnz is actually 1.decnz.f
# used to skip past the last set 1 on a reg to
# check if it can be decremented
1.decnz 1 1 L 1.decnz.g
# 1 [IP] 1 1.decnz.b> [>0 0s] 1 [REST OF FIRST REG]
# 1 [IP] 1 [>0 0s] 0 1.decnz.c> [REST OF FIRST REG]
1.decnz.b 0 0 R 1.decnz.b
1.decnz.b 1 0 R 1.decnz.c
# 1.decnz.d> [REG] 0
# 0 [REG] decnz.d>
#
# but once we reach the 00 selector we transition into decrement:
#
# 1.decnz.d> 0
# 0 decnz.e>
1.decnz.c 0 1 R 1.decnz.d
1.decnz.c 1 1 R 1.decnz.c
1.decnz.d 0 0 R 1.decnz.e
1.decnz.d 1 0 R 1.decnz.c
1.decnz.e 0 0 L 1.decnz
# Find end of register to decrement:
# decnz.e> [1s] 1 0
# [1s] 1 <1.decnz 0
# [1s] <1.decnz.g 1 0
1.decnz.e 1 1 R 1.decnz.e
# If decnz.g does not find more of the register we cannot decrement:
# Use the alternate return, otherwise move to the right to prepare
# to overwrite the last digit.
1.decnz.g 0 0 L 2.ret2
1.decnz.g 1 1 R 1.decnz.h
# Increment the next register
# (We shift the registers by incrementing to the left then degrementing
# on the right)
1.decnz.h 0 1 R 1.decnz.i
# Decrement the last register:
1.decnz.h 1 0 R 1.decnz.h
# check if we've reached the end of the register file:
# If so we'll use 1.sel to remove the register we just added.
# Otherwise we will transition into decrementing the current register
# (Which will restore it to it's old value shifted one cell to the left.)
1.decnz.i 0 0 L 1.sel
1.decnz.i 1 1 R 1.decnz.e
#
1.inc 0 1 R 1.inc.b
1.inc.b 0 0 R 1.inc.b
1.inc.b 1 1 R 1.inc.c
1.inc.c 0 0 R 1.inc.d
1.inc.c 1 1 R 1.inc.c
1.inc.d 0 1 L 2.ret1
1.inc.d 1 1 R 1.inc.c
#
1.sel 0 1 R 1.sel.b
# with a 1 on the tape 1.sel is actually 1.decnz.j
# used to clear the extra register added after the RF
1.sel 1 0 L 2.ret1
1.sel.b 0 0 R 1.sel.b
1.sel.b 1 1 R 1.sel.c
1.sel.c 0 0 R 1.sel.d
1.sel.c 1 1 R 1.sel.c
1.sel.d 0 0 L 1.sel.e
1.sel.d 1 1 R 1.sel.c
1.sel.e 0 1 L 1.sel.f
1.sel.e 1 0 L 2.ret1
1.sel.f 0 0 R 1.sel.e
1.sel.f 1 1 L 1.sel.f
#
2.ret1 0 0 L 2.ret1.1
2.ret1 1 1 L 2.ret1
2.ret1.1 0 0 L 2.ret1.2
2.ret1.1 1 1 L 2.ret1
# search for the marker after IP
2.ret1.2 0 0 L 2.ret1.2
2.ret1.2 1 0 L 6.break.0
#
2.ret2 0 0 L 2.ret2.1
2.ret2 1 1 L 2.ret2
2.ret2.1 0 0 L 2.ret2.2
2.ret2.1 1 1 L 2.ret2
# search for the marker after IP
2.ret2.2 0 0 L 2.ret2.2
2.ret2.2 1 0 L 6.break.1
3.axiomcode.decnz 0 0 R 1.sel
3.axiomcode.decnz 1 1 R 3.wffstack.decnz
3.axiomcode.inc 0 0 R 1.sel
3.axiomcode.inc 1 1 R 3.wffstack.inc
3.nextproof.decnz 0 0 R 1.sel
3.nextproof.decnz 1 1 R 1.decnz
3.nextproof.inc 0 0 R 1.sel
3.nextproof.inc 1 1 R 1.inc
3.param1.decnz 0 0 R 1.sel
3.param1.decnz 1 1 R 3.axiomcode.decnz
3.param1.inc 0 0 R 1.sel
3.param1.inc 1 1 R 3.axiomcode.inc
3.param2.decnz 0 0 R 1.sel
3.param2.decnz 1 1 R 3.param1.decnz
3.param2.inc 0 0 R 1.sel
3.param2.inc 1 1 R 3.param1.inc
3.prooflist.decnz 0 0 R 1.sel
3.prooflist.decnz 1 1 R 3.scratch2.decnz
3.prooflist.inc 0 0 R 1.sel
3.prooflist.inc 1 1 R 3.scratch2.inc
3.scratch1.decnz 0 0 R 1.sel
3.scratch1.decnz 1 1 R 3.param2.decnz
3.scratch1.inc 0 0 R 1.sel
3.scratch1.inc 1 1 R 3.param2.inc
3.scratch2.decnz 0 0 R 1.sel
3.scratch2.decnz 1 1 R 3.scratch1.decnz
3.scratch2.inc 0 0 R 1.sel
3.scratch2.inc 1 1 R 3.scratch1.inc
3.topwff.decnz 0 0 R 1.sel
3.topwff.decnz 1 1 R 3.nextproof.decnz
3.topwff.inc 0 0 R 1.sel
3.topwff.inc 1 1 R 3.nextproof.inc
3.wffstack.decnz 0 0 R 1.sel
3.wffstack.decnz 1 1 R 3.topwff.decnz
3.wffstack.inc 0 0 R 1.sel
3.wffstack.inc 1 1 R 3.topwff.inc
#
# 4. dispatch
#
# Find the start of the IP. We pass by a set number of 0 cells going
# left (how many depends on the decision tree), then scan right for the
# first 1 cell.
#
4.dispatch.1 0 0 L 4.dispatch.2
4.dispatch.1 1 1 L 6.continue.0
4.dispatch.2 0 0 L 4.dispatch.3
4.dispatch.2 1 1 L 6.continue.0
4.dispatch.3 0 0 L 4.dispatch.4
4.dispatch.3 1 1 L 6.continue.0
4.dispatch.4 0 0 L 4.dispatch.5
4.dispatch.4 1 1 L 6.continue.0
4.dispatch.5 0 0 L 4.dispatch.6
4.dispatch.5 1 1 L 6.continue.0
4.dispatch.6 0 0 L 4.dispatch.7
4.dispatch.6 1 1 L 6.continue.0
4.dispatch.7 0 0 L 4.dispatch.8
4.dispatch.7 1 1 L 6.continue.0
4.dispatch.8 0 0 L 4.dispatch.9
4.dispatch.8 1 1 L 6.continue.0
4.dispatch.9 0 0 R 5.root
4.dispatch.9 1 1 L 6.continue.0
#
# 5. root - find the root of the IP
#
# There is no special handling to call main() in a loop. At the end
# of main() the IP simply overflows past the marker to the left of the
# IP and creates a new marker with the IP all zeros.
#
5.root 0 0 R 5.root
5.root 1 1 R main().0
#
# 6. IP jump instructions.
#
6.break.0 0 1 L 6.continue.0
6.break.0 1 0 L 6.break.0
6.break.1 0 0 L 6.break.0
6.break.1 1 0 L 6.break.1
6.break.2 0 0 L 6.break.1
6.break.2 1 0 L 6.break.2
6.break.3 0 0 L 6.break.2
6.break.3 1 0 L 6.break.3
6.continue.0 0 0 L 4.dispatch.1
6.continue.0 1 1 L 6.continue.0
6.continue.1 0 0 L 6.continue.1
6.continue.1 1 0 L 6.continue.0
6.continue.2 0 0 L 6.continue.2
6.continue.2 1 0 L 6.continue.1
6.continue.3 0 0 L 6.continue.3
6.continue.3 1 0 L 6.continue.2
6.continue.4 0 0 L 6.continue.4
6.continue.4 1 0 L 6.continue.3
axioms().0 0 0 R axioms().n_187.0
axioms().0 1 1 R axioms().1
axioms().1 0 0 R read(param2).0
axioms().1 1 1 R axioms().2
axioms().2 0 0 R axioms().n_165.0
axioms().2 1 1 R axioms().3
axioms().3 0 0 R wel().0
axioms().3 1 1 R axioms().4
axioms().4 0 0 R axioms().n_173.0
axioms().4 1 1 R axioms().5
axioms().5 0 0 R wel().0
axioms().5 1 1 R axioms().6
axioms().6 0 0 R axioms().n_189.0
axioms().6 1 1 R axioms().7
axioms().7 0 0 R axioms().n_165.0
axioms().7 1 1 R axioms().8
axioms().8 0 0 R wn().0
axioms().8 1 1 R axioms().9
axioms().9 0 0 R axioms().n_168.0
axioms().9 1 1 R axioms().10
axioms().10 0 0 R axioms().n_196.0
axioms().10 1 1 R axioms().11
axioms().11 0 0 R axioms().n_187.0
axioms().11 1 1 R axioms().12
axioms().12 0 0 R wex().0
axioms().12 1 1 R axioms().13
axioms().13 0 0 R fn_59().0
axioms().13 1 1 R axioms().14
axioms().14 0 0 R axioms().n_171.0
axioms().14 1 1 R axioms().15
axioms().15 0 0 R axioms().n_203.0
axioms().15 1 1 R axioms().16
axioms().16 0 0 R par3().0
axioms().16 1 1 R axioms().17
axioms().17 0 0 R axioms().n_190.0
axioms().17 1 1 R axioms().18
axioms().18 0 0 R axioms().n_170.0
axioms().18 1 1 R axioms().19
axioms().19 0 0 R axioms().n_163.0
axioms().19 1 1 R axioms().20
axioms().20 0 0 R axioms().n_195.0
axioms().20 1 1 R axioms().21
axioms().21 0 0 R axioms().n_167.0
axioms().21 1 1 R axioms().22
axioms().22 0 0 R axioms().n_163.0
axioms().22 1 1 R axioms().23
axioms().23 0 0 R pushwff().0
axioms().23 1 1 R axioms().24
axioms().24 0 0 R axioms().n_184.0
axioms().24 1 1 R axioms().25
axioms().25 0 0 R axioms().n_162.0
axioms().25 1 1 R axioms().26
axioms().26 0 0 R axioms().n_166.0
axioms().26 1 1 R axioms().27
axioms().27 0 0 R axioms().n_188.0
axioms().27 1 1 R axioms().28
axioms().28 0 0 R v_2().0
axioms().28 1 1 R axioms().29
axioms().29 0 0 R axioms().n_188.0
axioms().29 1 1 R axioms().30
axioms().30 0 0 R axioms().n_161.0
axioms().30 1 1 R axioms().31
axioms().31 0 0 R node_201.0
axioms().31 1 1 R axioms().32
axioms().32 0 0 R axioms().n_160.0
axioms().32 1 1 R axioms().33
axioms().33 0 0 R axioms().n_214.0
axioms().33 1 1 R axioms().34
axioms().34 0 0 R axioms().n_161.0
axioms().34 1 1 R axioms().35
axioms().35 0 0 R axioms().n_160.0
axioms().35 1 1 R axioms().36
axioms().36 0 0 R axioms().n_166.0
axioms().36 1 1 R axioms().37
axioms().37 0 0 R axioms().n_213.0
axioms().37 1 1 R axioms().38
axioms().38 0 0 R v_4().0
axioms().38 1 1 R axioms().39
axioms().39 0 0 R axioms().n_183.0
axioms().39 1 1 R axioms().40
axioms().40 0 0 R wel().0
axioms().40 1 1 R axioms().41
axioms().41 0 0 R axioms().n_164.0
axioms().41 1 1 R axioms().42
axioms().42 0 0 R weq().0
axioms().42 1 1 R axioms().43
axioms().43 0 0 R node_212.0
axioms().43 1 1 R axioms().44
axioms().44 0 0 R axioms().44.0
axioms().44 1 1 R axioms().45
axioms().44.0 0 0 R wn().0
axioms().44.0 1 1 R wex().0
axioms().45 0 0 R wex().0
axioms().45 1 1 R axioms().46
axioms().46 0 0 R axioms().n_208.0
axioms().46 1 1 R axioms().47
axioms().47 0 0 R wn().0
axioms().47 1 1 R axioms().48
axioms().48 0 0 R axioms().n_165.0
axioms().48 1 1 R axioms().49
axioms().49 0 0 R axioms().n_203.0
axioms().49 1 1 R axioms().50
axioms().50 0 0 R pushwff().0
axioms().50 1 1 R axioms().51
axioms().51 0 0 R axioms().n_168.0
axioms().51 1 1 R axioms().52
axioms().52 0 0 R wal().0
axioms().52 1 1 R axioms().53
axioms().53 0 0 R wel().0
axioms().53 1 1 R axioms().54
axioms().54 0 0 R weq().0
axioms().54 1 1 R axioms().55
axioms().55 0 0 R axioms().n_204.0
axioms().55 1 1 R axioms().56
axioms().56 0 0 R axioms().n_204.0
axioms().56 1 1 R axioms().57
axioms().57 0 0 R axioms().n_193.0
axioms().57 1 1 R axioms().58
axioms().58 0 0 R axioms().n_209.0
axioms().58 1 1 R axioms().59
axioms().59 0 0 R par1().0
axioms().59 1 1 R axioms().60
axioms().60 0 0 R axioms().n_191.0
axioms().60 1 1 R axioms().61
axioms().61 0 0 R wn().0
axioms().61 1 1 R axioms().62
axioms().62 0 0 R fn_59().0
axioms().62 1 1 R axioms().63
axioms().63 0 0 R axioms().n_189.0
axioms().63 1 1 R axioms().64
axioms().64 0 0 R axioms().n_171.0
axioms().64 1 1 R axioms().65
axioms().65 0 0 R wel().0
axioms().65 1 1 R axioms().66
axioms().66 0 0 R axioms().n_206.0
axioms().66 1 1 R axioms().67
axioms().67 0 0 R axioms().n_172.0
axioms().67 1 1 R axioms().68
axioms().68 0 0 R wal().0
axioms().68 1 1 R axioms().69
axioms().69 0 0 R axioms().n_203.0
axioms().69 1 1 R axioms().70
axioms().70 0 0 R axioms().n_192.0
axioms().70 1 1 R axioms().71
axioms().71 0 0 R axioms().n_211.0
axioms().71 1 1 R axioms().72
axioms().72 0 0 R pushwff().0
axioms().72 1 1 R axioms().73
axioms().73 0 0 R axioms().n_194.0
axioms().73 1 1 R axioms().74
axioms().74 0 0 R wel().0
axioms().74 1 1 R axioms().75
axioms().75 0 0 R axioms().n_176.0
axioms().75 1 1 R axioms().76
axioms().76 0 0 R pushwff().0
axioms().76 1 1 R axioms().77
axioms().77 0 0 R node_200.0
axioms().77 1 1 R axioms().78
axioms().78 0 0 R while_decnz(scratch1,3.topwff.inc).0
axioms().78 1 1 R axioms().79
axioms().79 0 0 R fn_45().0
axioms().79 1 1 R axioms().80
axioms().80 0 0 R node_205.0
axioms().80 1 1 R axioms().81
axioms().81 0 0 R axioms().n_216.0
axioms().81 1 1 R axioms().82
axioms().82 0 0 R fn_45().0
axioms().82 1 1 R axioms().83
axioms().83 0 0 R axioms().n_206.0
axioms().83 1 1 R axioms().84
axioms().84 0 0 R fn_45().0
axioms().84 1 1 R axioms().85
axioms().85 0 0 R axioms().n_169.0
axioms().85 1 1 R axioms().86
axioms().86 0 0 R wal().0
axioms().86 1 1 R axioms().87
axioms().87 0 0 R axioms().n_207.0
axioms().87 1 1 R axioms().88
axioms().88 0 0 R axioms().n_190.0
axioms().88 1 1 R axioms().89
axioms().89 0 0 R axioms().n_215.0
axioms().89 1 1 R axioms().90
axioms().90 0 0 R axioms().n_217.0
axioms().90 1 1 R axioms().91
axioms().91 0 0 R axioms().n_191.0
axioms().91 1 1 R axioms().92
axioms().92 0 0 R axioms().n_210.0
axioms().92 1 1 R axioms().93
axioms().93 0 0 R axioms().n_169.0
axioms().93 1 1 R axioms().94
axioms().94 0 0 R wel().0
axioms().94 1 1 R axioms().95
axioms().95 0 0 R axioms().n_207.0
axioms().95 1 1 R axioms().96
axioms().96 0 0 R axioms().n_172.0
axioms().96 1 1 R axioms().97
axioms().97 0 0 R axioms().n_208.0
axioms().97 1 1 R axioms().98
axioms().98 0 0 R axioms().n_187.0
axioms().98 1 1 R axioms().99
axioms().99 0 0 R axioms().n_192.0
axioms().99 1 1 R axioms().100
axioms().100 0 0 R fn_45().0
axioms().100 1 1 R axioms().101
axioms().101 0 0 R axioms().n_218.0
axioms().101 1 1 R axioms().102
axioms().102 0 0 R axioms().n_173.0
axioms().102 1 1 R axioms().103
axioms().103 0 0 R axioms().n_209.0
axioms().103 1 1 R axioms().104
axioms().104 0 0 R pushwff().0
axioms().104 1 1 R axioms().105
axioms().105 0 0 R axioms().n_197.0
axioms().105 1 1 R axioms().106
axioms().106 0 0 R wal().0
axioms().106 1 1 R axioms().107
axioms().107 0 0 R axioms().n_199.0
axioms().107 1 1 R axioms().108
axioms().108 0 0 R axioms().n_174.0
axioms().108 1 1 R axioms().109
axioms().109 0 0 R wn().0
axioms().109 1 1 R axioms().110
axioms().110 0 0 R axioms().n_180.0
axioms().110 1 1 R axioms().111
axioms().111 0 0 R axioms().n_193.0
axioms().111 1 1 R axioms().112
axioms().112 0 0 R axioms().n_182.0
axioms().112 1 1 R axioms().113
axioms().113 0 0 R par3().0
axioms().113 1 1 R axioms().114
axioms().114 0 0 R axioms().n_194.0
axioms().114 1 1 R axioms().115
axioms().115 0 0 R axioms().n_174.0
axioms().115 1 1 R axioms().116
axioms().116 0 0 R axioms().n_180.0
axioms().116 1 1 R axioms().117
axioms().117 0 0 R axioms().n_176.0
axioms().117 1 1 R axioms().118
axioms().118 0 0 R axioms().118.0
axioms().118 1 1 R axioms().119
axioms().118.0 0 0 R axioms().n_208.0
axioms().118.0 1 1 R axioms().n_208.0
axioms().119 0 0 R axioms().n_182.0
axioms().119 1 1 R axioms().120
axioms().120 0 0 R wal().0
axioms().120 1 1 R axioms().121
axioms().121 0 0 R axioms().n_169.0
axioms().121 1 1 R axioms().122
axioms().122 0 0 R axioms().n_210.0
axioms().122 1 1 R axioms().123
axioms().123 0 0 R axioms().n_211.0
axioms().123 1 1 R axioms().124
axioms().124 0 0 R wa().0
axioms().124 1 1 R occgate().0
axioms().n_160.0 0 0 R axioms().n_183.0
axioms().n_160.0 1 1 R axioms().n_160.1
axioms().n_160.1 0 0 R v_4().0
axioms().n_160.1 1 1 R axioms().n_160.2
axioms().n_160.2 0 0 R axioms().n_213.0
axioms().n_160.2 1 1 R axioms().n_160.3
axioms().n_160.3 0 0 R axioms().n_195.0
axioms().n_160.3 1 1 R axioms().n_160.4
axioms().n_160.4 0 0 R axioms().n_219.0
axioms().n_160.4 1 1 R axioms().n_160.5
axioms().n_160.5 0 0 R v_4().0
axioms().n_160.5 1 1 R axioms().n_160.6
axioms().n_160.6 0 0 R axioms().n_175.0
axioms().n_160.6 1 1 R axioms().n_160.7
axioms().n_160.7 0 0 R wn().0
axioms().n_160.7 1 1 R axioms().n_160.8
axioms().n_160.8 0 0 R v_2().0
axioms().n_160.8 1 1 R axioms().n_160.9
axioms().n_160.9 0 0 R axioms().n_175.0
axioms().n_160.9 1 1 R axioms().n_160.10
axioms().n_160.10 0 0 R fn_45().0
axioms().n_160.10 1 1 R axioms().n_160.11
axioms().n_160.11 0 0 R axioms().n_208.0
axioms().n_160.11 1 1 R axioms().n_160.12
axioms().n_160.12 0 0 R wal().0
axioms().n_160.12 1 1 R wa().0
axioms().n_161.0 0 0 R axioms().n_183.0
axioms().n_161.0 1 1 R axioms().n_161.1
axioms().n_161.1 0 0 R pushwff().0
axioms().n_161.1 1 1 R axioms().n_161.2
axioms().n_161.2 0 0 R axioms().n_162.0
axioms().n_161.2 1 1 R axioms().n_161.3
axioms().n_161.3 0 0 R v_4().0
axioms().n_161.3 1 1 R axioms().n_214.0
axioms().n_162.0 0 0 R axioms().n_184.0
axioms().n_162.0 1 1 R axioms().n_167.0
axioms().n_163.0 0 0 R v_2().0
axioms().n_163.0 1 1 R axioms().n_164.0
axioms().n_164.0 0 0 R axioms().n_170.0
axioms().n_164.0 1 1 R axioms().n_213.0
axioms().n_165.0 0 0 R axioms().n_178.0
axioms().n_165.0 1 1 R axioms().n_198.0
axioms().n_166.0 0 0 R wa().0
axioms().n_166.0 1 1 R axioms().n_177.0
axioms().n_167.0 0 0 R axioms().n_195.0
axioms().n_167.0 1 1 R axioms().n_167.1
axioms().n_167.1 0 0 R wel().0
axioms().n_167.1 1 1 R axioms().n_209.0
axioms().n_168.0 0 0 R weq().0
axioms().n_168.0 1 1 R axioms().n_173.0
axioms().n_169.0 0 0 R fn_45().0
axioms().n_169.0 1 1 R axioms().n_169.1
axioms().n_169.1 0 0 R axioms().n_185.0
axioms().n_169.1 1 1 R axioms().n_215.0
axioms().n_170.0 0 0 R axioms().n_177.0
axioms().n_170.0 1 1 R node_201.0
axioms().n_171.0 0 0 R axioms().n_185.0
axioms().n_171.0 1 1 R axioms().n_216.0
axioms().n_172.0 0 0 R wel().0
axioms().n_172.0 1 1 R axioms().n_172.1
axioms().n_172.1 0 0 R axioms().n_196.0
axioms().n_172.1 1 1 R axioms().n_206.0
axioms().n_173.0 0 0 R axioms().n_197.0
axioms().n_173.0 1 1 R axioms().n_198.0
axioms().n_174.0 0 0 R axioms().n_178.0
axioms().n_174.0 1 1 R weq().0
axioms().n_175.0 0 0 R axioms().n_199.0
axioms().n_175.0 1 1 R axioms().n_189.0
axioms().n_176.0 0 0 R axioms().n_194.0
axioms().n_176.0 1 1 R axioms().n_217.0
axioms().n_177.0 0 0 R v_4().0
axioms().n_177.0 1 1 R node_042.0
axioms().n_178.0 0 0 R axioms().n_197.0
axioms().n_178.0 1 1 R wn().0
axioms().n_180.0 0 0 R par1().0
axioms().n_180.0 1 1 R axioms().n_197.0
axioms().n_182.0 0 0 R axioms().n_208.0
axioms().n_182.0 1 1 R axioms().n_216.0
axioms().n_183.0 0 0 R node_201.0
axioms().n_183.0 1 1 R axioms().n_213.0
axioms().n_184.0 0 0 R wn().0
axioms().n_184.0 1 1 R wn().0
axioms().n_185.0 0 0 R axioms().n_218.0
axioms().n_185.0 1 1 R axioms().n_210.0
axioms().n_187.0 0 0 R par1().0
axioms().n_187.0 1 1 R axioms().n_187.1
axioms().n_187.1 0 0 R fn_59().0
axioms().n_187.1 1 1 R wal().0
axioms().n_188.0 0 0 R v_4().0
axioms().n_188.0 1 1 R node_201.0
axioms().n_189.0 0 0 R wn().0
axioms().n_189.0 1 1 R weq().0
axioms().n_190.0 0 0 R axioms().n_219.0
axioms().n_190.0 1 1 R fn_45().0
axioms().n_191.0 0 0 R axioms().n_210.0
axioms().n_191.0 1 1 R par1().0
axioms().n_192.0 0 0 R axioms().n_216.0
axioms().n_192.0 1 1 R wal().0
axioms().n_193.0 0 0 R axioms().n_213.0
axioms().n_193.0 1 1 R par3().0
axioms().n_194.0 0 0 R par3().0
axioms().n_194.0 1 1 R axioms().n_213.0
axioms().n_195.0 0 0 R v_2().0
axioms().n_195.0 1 1 R axioms().n_213.0
axioms().n_196.0 0 0 R weq().0
axioms().n_196.0 1 1 R axioms().n_218.0
axioms().n_197.0 0 0 R par1().0
axioms().n_197.0 1 1 R axioms().n_213.0
axioms().n_198.0 0 0 R fn_59().0
axioms().n_198.0 1 1 R axioms().n_213.0
axioms().n_199.0 0 0 R axioms().n_213.0
axioms().n_199.0 1 1 R pushwff().0
axioms().n_203.0 0 0 R wal().0
axioms().n_203.0 1 1 R fn_59().0
axioms().n_204.0 0 0 R par3().0
axioms().n_204.0 1 1 R 3.topwff.inc
axioms().n_206.0 0 0 R fn_59().0
axioms().n_206.0 1 1 R par3().0
axioms().n_207.0 0 0 R par3().0
axioms().n_207.0 1 1 R fn_59().0
axioms().n_208.0 0 0 R fn_45().0
axioms().n_208.0 1 1 R wal().0
axioms().n_209.0 0 0 R weq().0
axioms().n_209.0 1 1 R wex().0
axioms().n_210.0 0 0 R fn_59().0
axioms().n_210.0 1 1 R weq().0
axioms().n_211.0 0 0 R wal().0
axioms().n_211.0 1 1 R fn_45().0
axioms().n_213.0 0 0 R pushwff().0
axioms().n_213.0 1 1 R weq().0
axioms().n_214.0 0 0 R v_2().0
axioms().n_214.0 1 1 R v_4().0
axioms().n_215.0 0 0 R par3().0
axioms().n_215.0 1 1 R par1().0
axioms().n_216.0 0 0 R par1().0
axioms().n_216.0 1 1 R par3().0
axioms().n_217.0 0 0 R weq().0
axioms().n_217.0 1 1 R par3().0
axioms().n_218.0 0 0 R fn_45().0
axioms().n_218.0 1 1 R par1().0
axioms().n_219.0 0 0 R wal().0
axioms().n_219.0 1 1 R weq().0
fn_105().0 0 0 R 3.param2.inc
fn_105().0 1 1 R fn_105().1
fn_105().1 0 0 R pair(scratch1,param2,param1).0
fn_105().1 1 1 R while_decnz(scratch1,3.param1.inc).0
fn_111().0 0 0 R 3.param1.decnz
fn_111().0 1 1 R fn_111().1
fn_111().1 0 0 R fn_111().1.0
fn_111().1 1 0 L 6.continue.1
fn_111().1.0 0 0 R 3.scratch1.inc
fn_111().1.0 1 1 R if_not_decnz(param2,47).0
fn_14().0 0 0 R 3.prooflist.decnz
fn_14().0 1 1 R node_013.0
fn_41().0 0 0 R 3.wffstack.decnz
fn_41().0 1 1 R node_013.0
fn_44().0 0 0 R 3.scratch2.decnz
fn_44().0 1 1 R fn_44().1
fn_44().1 0 0 R node_042.0
fn_44().1 1 0 L 6.continue.1
fn_45().0 0 0 R node_202.0
fn_45().0 1 1 R fn_45().1
fn_45().1 0 0 R pair(scratch2,scratch1,topwff).0
fn_45().1 1 1 R fn_44().0
fn_59().0 0 0 R pushwff().0
fn_59().0 1 1 R fn_59().1
fn_59().1 0 0 R while_decnz(param2,37).0
fn_59().1 1 1 R while_decnz(scratch1,3.param2.inc).0
fn_81().0 0 0 R 3.scratch1.decnz
fn_81().0 1 1 R fn_81().1
fn_81().1 0 0 R fn_81().1.0
fn_81().1 1 0 L 6.continue.1
fn_81().1.0 0 0 R 3.scratch2.inc
fn_81().1.0 1 1 R if_not_decnz(param2,76).0
if_eq().n_055.0 0 0 R if_eq().n_055.0.0
if_eq().n_055.0 1 1 R if_eq().n_055.1
if_eq().n_055.0.0 0 0 R 3.scratch1.decnz
if_eq().n_055.0.0 1 1 R if_eq().n_055.0.1
if_eq().n_055.0.1 0 0 R if_eq().n_055.0.1.0
if_eq().n_055.0.1 1 1 R if_eq().n_055.0.2
if_eq().n_055.0.1.0 0 0 R 3.param2.decnz
if_eq().n_055.0.1.0 1 0 L 6.continue.1
if_eq().n_055.0.2 0 0 R while_decnz(scratch1,3.param2.inc).0
if_eq().n_055.0.2 1 1 R 3.param2.inc
if_eq().n_055.1 0 0 R 3.param2.decnz
if_eq().n_055.1 1 1 R if_eq().n_055.2
if_eq().n_055.2 0 0 R while_decnz(param2,()).0
if_eq().n_055.2 1 0 L 6.break.1
if_eq(param2,scratch1,85).0 0 0 R if_eq(param2,scratch1,85).0.0
if_eq(param2,scratch1,85).0 1 1 R while_decnz(topwff,()).0
if_eq(param2,scratch1,85).0.0 0 0 R if_eq(param2,scratch1,85).0.0.0
if_eq(param2,scratch1,85).0.0 1 1 R if_eq(param2,scratch1,85).0.1
if_eq(param2,scratch1,85).0.0.0 0 0 R 3.param2.decnz
if_eq(param2,scratch1,85).0.0.0 1 1 R if_eq(param2,scratch1,85).0.0.1
if_eq(param2,scratch1,85).0.0.1 0 0 R if_eq(param2,scratch1,85).0.0.1.0
if_eq(param2,scratch1,85).0.0.1 1 1 R if_eq(param2,scratch1,85).0.0.2
if_eq(param2,scratch1,85).0.0.1.0 0 0 R 3.scratch1.decnz
if_eq(param2,scratch1,85).0.0.1.0 1 0 L 6.continue.1
if_eq(param2,scratch1,85).0.0.2 0 0 R while_decnz(param2,3.scratch1.inc).0
if_eq(param2,scratch1,85).0.0.2 1 1 R 3.scratch1.inc
if_eq(param2,scratch1,85).0.1 0 0 R 3.scratch1.decnz
if_eq(param2,scratch1,85).0.1 1 1 R if_eq(param2,scratch1,85).0.2
if_eq(param2,scratch1,85).0.2 0 0 R while_decnz(scratch1,()).0
if_eq(param2,scratch1,85).0.2 1 0 L 6.break.1
if_eq(scratch1,param2,40).0 0 0 R if_eq().n_055.0
if_eq(scratch1,param2,40).0 1 1 R par1().0
if_eq(scratch1,param2,halt).0 0 0 R if_eq().n_055.0
if_eq(scratch1,param2,halt).0 1 1 R halt
if_not_decnz().n_077.0 0 0 R 3.param2.decnz
if_not_decnz().n_077.0 1 0 L 6.break.1
if_not_decnz(param2,47).0 0 0 R if_not_decnz().n_077.0
if_not_decnz(param2,47).0 1 1 R while_decnz(scratch1,3.param2.inc).0
if_not_decnz(param2,76).0 0 0 R if_not_decnz().n_077.0
if_not_decnz(param2,76).0 1 1 R while_decnz(scratch2,3.param2.inc).0
if_not_decnz(prooflist,5).0 0 0 R if_not_decnz(prooflist,5).0.0
if_not_decnz(prooflist,5).0 1 1 R if_not_decnz(prooflist,5).1
if_not_decnz(prooflist,5).0.0 0 0 R 3.prooflist.decnz
if_not_decnz(prooflist,5).0.0 1 0 L 6.break.1
if_not_decnz(prooflist,5).1 0 0 R while_decnz(nextproof,0).0
if_not_decnz(prooflist,5).1 1 1 R if_not_decnz(prooflist,5).2
if_not_decnz(prooflist,5).2 0 0 R while_decnz(scratch1,3.nextproof.inc).0
if_not_decnz(prooflist,5).2 1 1 R 3.nextproof.inc
if_not_decnz(scratch1,9).0 0 0 R if_not_decnz(scratch1,9).0.0
if_not_decnz(scratch1,9).0 1 1 R while_decnz(scratch2,3.scratch1.inc).0
if_not_decnz(scratch1,9).0.0 0 0 R 3.scratch1.decnz
if_not_decnz(scratch1,9).0.0 1 0 L 6.break.1
main().0 0 0 R if_not_decnz(prooflist,5).0
main().0 1 1 R main().1
main().1 0 0 R read(axiomcode).0
main().1 1 1 R main().2
main().2 0 0 R read(param1).0
main().2 1 1 R main().3
main().3 0 0 R main().3.0
main().3 1 1 R mp().0
main().3.0 0 0 R 3.axiomcode.decnz
main().3.0 1 1 R main().3.1
main().3.1 0 0 R main().3.1.0
main().3.1 1 0 L 6.break.1
main().3.1.0 0 0 R main().3.1.0.0
main().3.1.0 1 1 R fn_59().0
main().3.1.0.0 0 0 R 3.axiomcode.decnz
main().3.1.0.0 1 1 R main().3.1.0.1
main().3.1.0.1 0 0 R main().3.1.0.1.0
main().3.1.0.1 1 0 L 6.break.1
main().3.1.0.1.0 0 0 R main().3.1.0.1.0.0
main().3.1.0.1.0 1 1 R nip().0
main().3.1.0.1.0.0 0 0 R 3.axiomcode.decnz
main().3.1.0.1.0.0 1 1 R main().3.1.0.1.0.1
main().3.1.0.1.0.1 0 0 R axioms().0
main().3.1.0.1.0.1 1 0 L 6.break.1
mp().0 0 0 R node_205.0
mp().0 1 1 R mp().1
mp().1 0 0 R while_decnz(topwff,3.scratch1.inc).0
mp().1 1 1 R if_eq(scratch1,param2,40).0
nip().0 0 0 R 3.scratch1.inc
nip().0 1 1 R nip().1
nip().1 0 0 R if_eq(scratch1,param2,halt).0
nip().1 1 1 R pop(param2).0
node_013.0 0 0 R node_013.0.0
node_013.0 1 0 L 6.continue.1
node_013.0.0 0 0 R 3.scratch2.inc
node_013.0.0 1 1 R if_not_decnz(scratch1,9).0
node_042.0 0 0 R node_186.0
node_042.0 1 1 R 3.topwff.inc
node_186.0 0 0 R node_201.0
node_186.0 1 1 R 3.topwff.inc
node_200.0 0 0 R fn_14().0
node_200.0 1 1 R while_decnz(scratch2,3.prooflist.inc).0
node_201.0 0 0 R 3.topwff.inc
node_201.0 1 1 R 3.topwff.inc
node_202.0 0 0 R fn_41().0
node_202.0 1 1 R while_decnz(scratch2,3.wffstack.inc).0
node_205.0 0 0 R par1().0
node_205.0 1 1 R fn_45().0
node_212.0 0 0 R wn().0
node_212.0 1 1 R fn_45().0
node_220.0 0 0 R fn_81().0
node_220.0 1 1 R while_decnz(scratch2,()).0
occ_h_bin().0 0 0 R fn_81().0
occ_h_bin().0 1 1 R occ_h_bin().1
occ_h_bin().1 0 0 R fn_105().0
occ_h_bin().1 1 1 R occ_h_bin().2
occ_h_bin().2 0 0 R while_decnz(scratch2,3.param2.inc).0
occ_h_bin().2 1 1 R fn_105().0
occ_h_sigma().0 0 0 R node_220.0
occ_h_sigma().0 1 1 R fn_105().0
occ_h_var().0 0 0 R node_220.0
occ_h_var().0 1 1 R occ_h_var().1
occ_h_var().1 0 0 R while_decnz(axiomcode,26).0
occ_h_var().1 1 1 R occ_h_var().2
occ_h_var().2 0 0 R while_decnz(scratch2,3.axiomcode.inc).0
occ_h_var().2 1 1 R if_eq(param2,scratch1,85).0
occ_init().0 0 0 R 3.param1.inc
occ_init().0 1 1 R occ_init().1
occ_init().1 0 0 R pair(scratch1,param1,scratch2).0
occ_init().1 1 1 R occ_init().2
occ_init().2 0 0 R 3.param2.inc
occ_init().2 1 1 R pair(param1,param2,scratch1).0
occ_pop().0 0 0 R fn_111().0
occ_pop().0 1 1 R while_decnz(scratch1,3.param1.inc).0
occgate().0 0 0 R occ_init().0
occgate().0 1 1 R occgate().1
occgate().1 0 0 R occgate().1.0
occgate().1 1 1 R while_decnz(axiomcode,()).0
occgate().1.0 0 0 R occ_pop().0
occgate().1.0 1 1 R occgate().1.1
occgate().1.1 0 0 R 3.param2.decnz
occgate().1.1 1 1 R occgate().1.2
occgate().1.2 0 0 R occgate().1.2.0
occgate().1.2 1 0 L 6.continue.2
occgate().1.2.0 0 0 R 3.param2.decnz
occgate().1.2.0 1 1 R occgate().1.2.1
occgate().1.2.1 0 0 R 3.param2.inc
occgate().1.2.1 1 1 R occgate().1.2.2
occgate().1.2.2 0 0 R occgate().1.2.2.0
occgate().1.2.2 1 1 R occ_h_sigma().0
occgate().1.2.2.0 0 0 R 3.param2.decnz
occgate().1.2.2.0 1 1 R occgate().1.2.2.1
occgate().1.2.2.1 0 0 R occgate().1.2.2.1.0
occgate().1.2.2.1 1 1 R occgate().1.2.2.2
occgate().1.2.2.1.0 0 0 R 3.param2.decnz
occgate().1.2.2.1.0 1 1 R occgate().1.2.2.1.1
occgate().1.2.2.1.1 0 0 R occgate().1.2.2.1.1.0
occgate().1.2.2.1.1 1 1 R occgate().1.2.2.1.2
occgate().1.2.2.1.1.0 0 0 R 3.param2.decnz
occgate().1.2.2.1.1.0 1 1 R occgate().1.2.2.1.1.1
occgate().1.2.2.1.1.1 0 0 R occgate().1.2.2.1.1.1.0
occgate().1.2.2.1.1.1 1 1 R occgate().1.2.2.1.1.2
occgate().1.2.2.1.1.1.0 0 0 R 3.param2.decnz
occgate().1.2.2.1.1.1.0 1 1 R occgate().1.2.2.1.1.1.1
occgate().1.2.2.1.1.1.1 0 0 R 3.scratch1.inc
occgate().1.2.2.1.1.1.1 1 0 L 6.continue.4
occgate().1.2.2.1.1.2 0 0 R occ_h_var().0
occgate().1.2.2.1.1.2 1 0 L 6.break.3
occgate().1.2.2.1.2 0 0 R occ_h_bin().0
occgate().1.2.2.1.2 1 0 L 6.break.2
occgate().1.2.2.2 0 0 R occ_h_bin().0
occgate().1.2.2.2 1 0 L 6.break.1
pair(param1,param2,scratch1).0 0 0 R while_decnz(scratch1,122).0
pair(param1,param2,scratch1).0 1 1 R pair(param1,param2,scratch1).1
pair(param1,param2,scratch1).1 0 0 R 3.param2.decnz
pair(param1,param2,scratch1).1 1 1 R pair(param1,param2,scratch1).2
pair(param1,param2,scratch1).2 0 0 R pair(param1,param2,scratch1).2.0
pair(param1,param2,scratch1).2 1 0 L 6.continue.2
pair(param1,param2,scratch1).2.0 0 0 R 3.param1.inc
pair(param1,param2,scratch1).2.0 1 1 R while_decnz(param2,3.scratch1.inc).0
pair(scratch1,param1,scratch2).0 0 0 R while_decnz(scratch2,113).0
pair(scratch1,param1,scratch2).0 1 1 R pair(scratch1,param1,scratch2).1
pair(scratch1,param1,scratch2).1 0 0 R 3.param1.decnz
pair(scratch1,param1,scratch2).1 1 1 R pair(scratch1,param1,scratch2).2
pair(scratch1,param1,scratch2).2 0 0 R pair(scratch1,param1,scratch2).2.0
pair(scratch1,param1,scratch2).2 1 0 L 6.continue.2
pair(scratch1,param1,scratch2).2.0 0 0 R 3.scratch1.inc
pair(scratch1,param1,scratch2).2.0 1 1 R while_decnz(param1,3.scratch2.inc).0
pair(scratch1,param2,param1).0 0 0 R while_decnz(param1,97).0
pair(scratch1,param2,param1).0 1 1 R pair(scratch1,param2,param1).1
pair(scratch1,param2,param1).1 0 0 R 3.param2.decnz
pair(scratch1,param2,param1).1 1 1 R pair(scratch1,param2,param1).2
pair(scratch1,param2,param1).2 0 0 R pair(scratch1,param2,param1).2.0
pair(scratch1,param2,param1).2 1 0 L 6.continue.2
pair(scratch1,param2,param1).2.0 0 0 R 3.scratch1.inc
pair(scratch1,param2,param1).2.0 1 1 R while_decnz(param2,3.param1.inc).0
pair(scratch2,scratch1,topwff).0 0 0 R while_decnz(topwff,26).0
pair(scratch2,scratch1,topwff).0 1 1 R pair(scratch2,scratch1,topwff).1
pair(scratch2,scratch1,topwff).1 0 0 R 3.scratch1.decnz
pair(scratch2,scratch1,topwff).1 1 1 R pair(scratch2,scratch1,topwff).2
pair(scratch2,scratch1,topwff).2 0 0 R pair(scratch2,scratch1,topwff).2.0
pair(scratch2,scratch1,topwff).2 1 0 L 6.continue.2
pair(scratch2,scratch1,topwff).2.0 0 0 R 3.scratch2.inc
pair(scratch2,scratch1,topwff).2.0 1 1 R while_decnz(scratch1,3.topwff.inc).0
par1().0 0 0 R pushwff().0
par1().0 1 1 R par1().1
par1().1 0 0 R while_decnz(param1,37).0
par1().1 1 1 R while_decnz(scratch1,3.param1.inc).0
par3().0 0 0 R pushwff().0
par3().0 1 1 R par3().1
par3().1 0 0 R while_decnz(axiomcode,37).0
par3().1 1 1 R while_decnz(scratch1,3.axiomcode.inc).0
pop(param2).0 0 0 R node_202.0
pop(param2).0 1 1 R while_decnz(scratch1,3.param2.inc).0
pushwff().0 0 0 R while_decnz(topwff,3.scratch1.inc).0
pushwff().0 1 1 R pushwff().1
pushwff().1 0 0 R while_decnz(wffstack,3.topwff.inc).0
pushwff().1 1 1 R pushwff().2
pushwff().2 0 0 R pair(scratch2,scratch1,topwff).0
pushwff().2 1 1 R while_decnz(scratch2,3.wffstack.inc).0
read(axiomcode).0 0 0 R node_200.0
read(axiomcode).0 1 1 R while_decnz(scratch1,3.axiomcode.inc).0
read(param1).0 0 0 R node_200.0
read(param1).0 1 1 R while_decnz(scratch1,3.param1.inc).0
read(param2).0 0 0 R node_200.0
read(param2).0 1 1 R while_decnz(scratch1,3.param2.inc).0
v_1().0 0 0 R pushwff().0
v_1().0 1 1 R 3.topwff.inc
v_2().0 0 0 R v_1().0
v_2().0 1 1 R 3.topwff.inc
v_4().0 0 0 R v_2().0
v_4().0 1 1 R node_201.0
wa().0 0 0 R node_212.0
wa().0 1 1 R wn().0
wal().0 0 0 R fn_45().0
wal().0 1 1 R node_201.0
wel().0 0 0 R fn_45().0
wel().0 1 1 R 3.topwff.inc
weq().0 0 0 R fn_45().0
weq().0 1 1 R node_186.0
wex().0 0 0 R wn().0
wex().0 1 1 R wex().1
wex().1 0 0 R wal().0
wex().1 1 1 R wn().0
while_decnz().n_008.0 0 0 R 3.scratch1.inc
while_decnz().n_008.0 1 0 L 6.continue.1
while_decnz().n_017.0 0 0 R 3.axiomcode.inc
while_decnz().n_017.0 1 0 L 6.continue.1
while_decnz().n_020.0 0 0 R 3.param1.inc
while_decnz().n_020.0 1 0 L 6.continue.1
while_decnz().n_024.0 0 0 R 3.topwff.inc
while_decnz().n_024.0 1 0 L 6.continue.1
while_decnz().n_027.0 0 0 R while_decnz().n_027.0.0
while_decnz().n_027.0 1 0 L 6.continue.1
while_decnz().n_027.0.0 0 0 R 3.scratch1.inc
while_decnz().n_027.0.0 1 1 R 3.scratch2.inc
while_decnz().n_038.0 0 0 R while_decnz().n_038.0.0
while_decnz().n_038.0 1 0 L 6.continue.1
while_decnz().n_038.0.0 0 0 R 3.scratch1.inc
while_decnz().n_038.0.0 1 1 R 3.topwff.inc
while_decnz().n_046.0 0 0 R 3.param2.inc
while_decnz().n_046.0 1 0 L 6.continue.1
while_decnz(axiomcode,()).0 0 0 R 3.axiomcode.decnz
while_decnz(axiomcode,()).0 1 0 L 6.continue.0
while_decnz(axiomcode,26).0 0 0 R 3.axiomcode.decnz
while_decnz(axiomcode,26).0 1 1 R while_decnz().n_027.0
while_decnz(axiomcode,37).0 0 0 R 3.axiomcode.decnz
while_decnz(axiomcode,37).0 1 1 R while_decnz().n_038.0
while_decnz(nextproof,0).0 0 0 R 3.nextproof.decnz
while_decnz(nextproof,0).0 1 1 R while_decnz(nextproof,0).1
while_decnz(nextproof,0).1 0 0 R while_decnz(nextproof,0).1.0
while_decnz(nextproof,0).1 1 0 L 6.continue.1
while_decnz(nextproof,0).1.0 0 0 R 3.prooflist.inc
while_decnz(nextproof,0).1.0 1 1 R 3.scratch1.inc
while_decnz(param1,3.scratch2.inc).0 0 0 R 3.param1.decnz
while_decnz(param1,3.scratch2.inc).0 1 1 R while_decnz(param1,3.scratch2.inc).1
while_decnz(param1,3.scratch2.inc).1 0 0 R 3.scratch2.inc
while_decnz(param1,3.scratch2.inc).1 1 0 L 6.continue.1
while_decnz(param1,37).0 0 0 R 3.param1.decnz
while_decnz(param1,37).0 1 1 R while_decnz().n_038.0
while_decnz(param1,97).0 0 0 R 3.param1.decnz
while_decnz(param1,97).0 1 1 R while_decnz(param1,97).1
while_decnz(param1,97).1 0 0 R while_decnz(param1,97).1.0
while_decnz(param1,97).1 1 0 L 6.continue.1
while_decnz(param1,97).1.0 0 0 R 3.param2.inc
while_decnz(param1,97).1.0 1 1 R 3.scratch1.inc
while_decnz(param2,()).0 0 0 R 3.param2.decnz
while_decnz(param2,()).0 1 0 L 6.continue.0
while_decnz(param2,3.param1.inc).0 0 0 R 3.param2.decnz
while_decnz(param2,3.param1.inc).0 1 1 R while_decnz().n_020.0
while_decnz(param2,3.scratch1.inc).0 0 0 R 3.param2.decnz
while_decnz(param2,3.scratch1.inc).0 1 1 R while_decnz().n_008.0
while_decnz(param2,37).0 0 0 R 3.param2.decnz
while_decnz(param2,37).0 1 1 R while_decnz().n_038.0
while_decnz(scratch1,()).0 0 0 R 3.scratch1.decnz
while_decnz(scratch1,()).0 1 0 L 6.continue.0
while_decnz(scratch1,122).0 0 0 R 3.scratch1.decnz
while_decnz(scratch1,122).0 1 1 R while_decnz(scratch1,122).1
while_decnz(scratch1,122).1 0 0 R while_decnz(scratch1,122).1.0
while_decnz(scratch1,122).1 1 0 L 6.continue.1
while_decnz(scratch1,122).1.0 0 0 R 3.param2.inc
while_decnz(scratch1,122).1.0 1 1 R 3.param1.inc
while_decnz(scratch1,3.axiomcode.inc).0 0 0 R 3.scratch1.decnz
while_decnz(scratch1,3.axiomcode.inc).0 1 1 R while_decnz().n_017.0
while_decnz(scratch1,3.nextproof.inc).0 0 0 R 3.scratch1.decnz
while_decnz(scratch1,3.nextproof.inc).0 1 1 R while_decnz(scratch1,3.nextproof.inc).1
while_decnz(scratch1,3.nextproof.inc).1 0 0 R 3.nextproof.inc
while_decnz(scratch1,3.nextproof.inc).1 1 0 L 6.continue.1
while_decnz(scratch1,3.param1.inc).0 0 0 R 3.scratch1.decnz
while_decnz(scratch1,3.param1.inc).0 1 1 R while_decnz().n_020.0
while_decnz(scratch1,3.param2.inc).0 0 0 R 3.scratch1.decnz
while_decnz(scratch1,3.param2.inc).0 1 1 R while_decnz().n_046.0
while_decnz(scratch1,3.topwff.inc).0 0 0 R 3.scratch1.decnz
while_decnz(scratch1,3.topwff.inc).0 1 1 R while_decnz().n_024.0
while_decnz(scratch2,()).0 0 0 R 3.scratch2.decnz
while_decnz(scratch2,()).0 1 0 L 6.continue.0
while_decnz(scratch2,113).0 0 0 R 3.scratch2.decnz
while_decnz(scratch2,113).0 1 1 R while_decnz(scratch2,113).1
while_decnz(scratch2,113).1 0 0 R while_decnz(scratch2,113).1.0
while_decnz(scratch2,113).1 1 0 L 6.continue.1
while_decnz(scratch2,113).1.0 0 0 R 3.param1.inc
while_decnz(scratch2,113).1.0 1 1 R 3.scratch1.inc
while_decnz(scratch2,3.axiomcode.inc).0 0 0 R 3.scratch2.decnz
while_decnz(scratch2,3.axiomcode.inc).0 1 1 R while_decnz().n_017.0
while_decnz(scratch2,3.param2.inc).0 0 0 R 3.scratch2.decnz
while_decnz(scratch2,3.param2.inc).0 1 1 R while_decnz().n_046.0
while_decnz(scratch2,3.prooflist.inc).0 0 0 R 3.scratch2.decnz
while_decnz(scratch2,3.prooflist.inc).0 1 1 R while_decnz(scratch2,3.prooflist.inc).1
while_decnz(scratch2,3.prooflist.inc).1 0 0 R 3.prooflist.inc
while_decnz(scratch2,3.prooflist.inc).1 1 0 L 6.continue.1
while_decnz(scratch2,3.scratch1.inc).0 0 0 R 3.scratch2.decnz
while_decnz(scratch2,3.scratch1.inc).0 1 1 R while_decnz().n_008.0
while_decnz(scratch2,3.wffstack.inc).0 0 0 R 3.scratch2.decnz
while_decnz(scratch2,3.wffstack.inc).0 1 1 R while_decnz(scratch2,3.wffstack.inc).1
while_decnz(scratch2,3.wffstack.inc).1 0 0 R 3.wffstack.inc
while_decnz(scratch2,3.wffstack.inc).1 1 0 L 6.continue.1
while_decnz(topwff,()).0 0 0 R 3.topwff.decnz
while_decnz(topwff,()).0 1 0 L 6.continue.0
while_decnz(topwff,26).0 0 0 R 3.topwff.decnz
while_decnz(topwff,26).0 1 1 R while_decnz().n_027.0
while_decnz(topwff,3.scratch1.inc).0 0 0 R 3.topwff.decnz
while_decnz(topwff,3.scratch1.inc).0 1 1 R while_decnz().n_008.0
while_decnz(wffstack,3.topwff.inc).0 0 0 R 3.wffstack.decnz
while_decnz(wffstack,3.topwff.inc).0 1 1 R while_decnz().n_024.0
wn().0 0 0 R v_1().0
wn().0 1 1 R fn_45().0

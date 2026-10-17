(** * E2E_TG: end to end, the 296-state machine m254tg_wade.tm halts from the blank tape iff
    ZF + GU ("every set lies in a Grothendieck universe", set.mm df-gru) is inconsistent,
    and likewise for ZF + Reg + GU, ZF + AC + GU (ZFC + GU) and ZF + Reg + AC + GU.

    [halts], [c0]: busycoq's TM semantics; [tm]: M254TGT.ZFTM.tm, which [M254TGT.ZFTM.tm_table] proves
    equal to the literal table of TableTG.v; the TM layer's check compares that table with
    machine/m254tg_wade.tm (sha256 e9b63d8e...).

    Chain (namespaces: M254TGT = ../tm/coq, M254TGP = ../prog/coq, M254TGL = ../logic/coq,
    M254TG = ../settheory, M254TGA = ../ac):
      halts tm c0
        <-> rm_halts dagtg ([], regs0)    M254TGT.MainTM.tmtg_rm     (TM layer: list-zipper simulation)
        <-> enum_tg_halts                 M254TGP.MainTG.progtg      (program layer)
        <-> SUIR ⊢TC ⊥                    M254TGL.BridgeTG.enum_tg_SUIR (L1_TG + bridge_tg)
        <-> ZFc + GU ⊢TC ⊥                M254TG.SU_main.SU_equicons (quotient / relativization to ⋃V_α)
        <-> ZFc + AC + GU ⊢TC ⊥           M254TGA.AC_main.ZFCGU_equicons (relativization to L; GU holds
                                          in L by condensation below a universe ordinal)
      and likewise with Reg (M254TGA.AC_main.ZFCRGU_equicons); AC is ZF/stdzf_r3/zfc's Z_wo.ax_ac.

    Names are fully qualified: the library's notations clash with busycoq's. *)
From Undecidability.FOL Require Syntax.Core Syntax.BinSig Sets.Signatures Deduction.FullND.
From BusyCoq Require Import TM.
From M254TGT Require Import ZFTM.
From M254TGT Require MainTM.
From M254TGP Require MainTG.
From M254TGL Require EnumTG BridgeTG.
From M254TG Require SU_def SU_gu SU_main.
From M254TGA Require AC_main.
From ZFC Require Z_wo.
From ZF Require Std_iface.
From RegCon Require MinZF.

Notation tprv := Undecidability.FOL.Deduction.FullND.tprv.
Notation sig0 := Undecidability.FOL.Syntax.BinSig.sig_empty.
Notation zfp := Undecidability.FOL.Sets.Signatures.ZFSignature.ZF_pred_sig.
Notation fon := Undecidability.FOL.Syntax.Core.falsity_on.
Notation cls := Undecidability.FOL.Syntax.Core.class.
Notation bot := Undecidability.FOL.Syntax.Core.falsity.

(** the machine's own target theory *)
Theorem tg296_halts_iff_SUIR : halts tm c0 <-> @tprv sig0 zfp fon cls M254TG.SU_def.SUIR bot.
Proof.
  rewrite M254TGT.MainTM.tmtg_rm, M254TGP.MainTG.progtg.
  exact M254TGL.BridgeTG.enum_tg_SUIR.
Qed.

Theorem tg296_halts_iff_ZFGU :
  halts tm c0 <-> @tprv sig0 zfp fon cls (fun phi => ZF.Std_iface.ZFc phi \/ phi = M254TG.SU_gu.GU) bot.
Proof. rewrite tg296_halts_iff_SUIR. exact M254TG.SU_main.SU_equicons. Qed.

Theorem tg296_halts_iff_ZFRGU :
  halts tm c0 <-> @tprv sig0 zfp fon cls
    (fun phi => (ZF.Std_iface.ZFc phi \/ phi = RegCon.MinZF.ax_reg') \/ phi = M254TG.SU_gu.GU) bot.
Proof. rewrite tg296_halts_iff_SUIR. exact M254TG.SU_main.SU_equicons_R. Qed.

(** with the axiom of choice (Zermelo's choice-set form, ZF/stdzf_r3/zfc Z_wo.ax_ac) *)
Theorem tg296_halts_iff_ZFCGU :
  halts tm c0 <-> @tprv sig0 zfp fon cls
    (fun phi => (ZF.Std_iface.ZFc phi \/ phi = ZFC.Z_wo.ax_ac) \/ phi = M254TG.SU_gu.GU) bot.
Proof. rewrite tg296_halts_iff_ZFGU. symmetry. exact M254TGA.AC_main.ZFCGU_equicons. Qed.

Theorem tg296_halts_iff_ZFCRGU :
  halts tm c0 <-> @tprv sig0 zfp fon cls
    (fun phi => ((ZF.Std_iface.ZFc phi \/ phi = RegCon.MinZF.ax_reg') \/ phi = ZFC.Z_wo.ax_ac) \/ phi = M254TG.SU_gu.GU) bot.
Proof. rewrite tg296_halts_iff_ZFGU. symmetry. exact M254TGA.AC_main.ZFCRGU_equicons. Qed.

Check tg296_halts_iff_ZFGU.
Check tg296_halts_iff_ZFRGU.
Print M254TG.SU_gu.GU.
Print Assumptions tg296_halts_iff_ZFGU.
Print Assumptions tg296_halts_iff_ZFRGU.
Check tg296_halts_iff_ZFCGU.
Check tg296_halts_iff_ZFCRGU.
Print ZFC.Z_wo.ax_ac.
Print Assumptions tg296_halts_iff_ZFCGU.
Print Assumptions tg296_halts_iff_ZFCRGU.

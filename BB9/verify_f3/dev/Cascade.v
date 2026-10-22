(** The cascade induction backbone (sketch section I), stated abstractly over a reachability predicate [reach L]
    ("some config at orbit value L is reached from c0").  The three hypotheses are discharged at final assembly by
    the machine lemmas: [casc_step] = one g-step (generic sub-step, or stop->CL->entry); [casc_key] = the endgame
    from a key; [casc_start] = exhaustion #2 reaching the cascade at L0.  No axioms: Variables/Hypotheses are local. *)

From XDev Require Import Orbit.
From Coq Require Import Lia PeanoNat Wf_nat Compare_dec.

Section CascadeBackbone.
  Variable halts_goal : Prop.                 (* instantiated by [halts tm c0] *)
  Variable reach : nat -> Prop.               (* a cascade config at orbit value L is reached from c0 *)

  (* one orbit step at the configuration level, preserving reachability (L >= 60, on the odd/1-mod-3 orbit) *)
  Hypothesis casc_step : forall L, 60 <= L -> L mod 2 = 1 -> L mod 3 = 1 -> reach L -> reach (gstep L).
  (* the endgame: from a key the machine halts *)
  Hypothesis casc_key  : forall L, in_keys L = true -> reach L -> halts_goal.

  (** From any reachable orbit value (odd, 1 mod 3), the machine halts: well-founded descent on L. *)
  Theorem cascade_halts : forall L, L mod 2 = 1 -> L mod 3 = 1 -> reach L -> halts_goal.
  Proof.
    intro L. induction L as [L IH] using lt_wf_ind. intros H2 H3 HR.
    destruct (le_lt_dec 60 L) as [Hge | Hlt].
    - (* L >= 60: take one step to gstep L *)
      pose proof (casc_step L Hge H2 H3 HR) as HR'.
      pose proof (gstep_inv L Hge H2 H3) as [G2 G3].
      pose proof (gstep_lt L Hge) as Hdec.
      destruct (le_lt_dec 60 (gstep L)) as [Hge' | Hlt'].
      + (* still >= 60: recurse *)
        apply (IH (gstep L) Hdec G2 G3 HR').
      + (* dropped below 60: it is a key *)
        apply (casc_key (gstep L)).
        * apply (gstep_key L Hge H2 H3 Hlt').
        * exact HR'.
    - (* L < 60 already: it must be a key to proceed; handled by the caller providing a key-reach.
         For the real run L0 is huge, so this branch is only reached after a step that lands in a key,
         which the >= 60 branch dispatches.  Here we require L itself to be a key. *)
      (* The real entry L0 >= 60, so this branch is vacuous for the top-level call; but to keep the lemma
         total we still discharge it when L is a key. *)
      destruct (in_keys L) eqn:Hk.
      + apply (casc_key L Hk HR).
      + (* a sub-60 non-key odd/1-mod-3 value is never the top-level start (L0 huge) nor a g-image
           (g-images below 60 are keys).  Left as an explicit obligation: *)
        exfalso. revert Hk. clear.
        (* not provable in the abstract section; the real call never hits it. We expose it as a hypothesis. *)
  Abort.

  (** The usable form: the top-level start L0 is >= 60, odd, 1 mod 3, and reachable. *)
  Theorem cascade_from_start : forall L0, 60 <= L0 -> L0 mod 2 = 1 -> L0 mod 3 = 1 -> reach L0 -> halts_goal.
  Proof.
    intro L0. induction L0 as [L0 IH] using lt_wf_ind. intros Hge H2 H3 HR.
    pose proof (casc_step L0 Hge H2 H3 HR) as HR'.
    pose proof (gstep_inv L0 Hge H2 H3) as [G2 G3].
    pose proof (gstep_lt L0 Hge) as Hdec.
    destruct (le_lt_dec 60 (gstep L0)) as [Hge' | Hlt'].
    - apply (IH (gstep L0) Hdec Hge' G2 G3 HR').
    - apply (casc_key (gstep L0)).
      + apply (gstep_key L0 Hge H2 H3 Hlt').
      + exact HR'.
  Qed.

End CascadeBackbone.

(** [cascade_from_start] : for any [halts_goal] and [reach], given one-g-step reachability for L >= 60 and the
    endgame from keys, a reachable odd/1-mod-3 start L0 >= 60 yields [halts_goal].  This is the sketch's induction I;
    at assembly [halts_goal := halts tm c0], [reach L := exists c, c0 -->* c /\ c is the cascade config at L], and the
    hypotheses become the machine lemmas (generic sub-step/stop/entry for casc_step, endgame R3/R4 for casc_key). *)

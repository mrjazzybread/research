From iris.algebra Require Import frac gmap auth.
From iris.base_logic Require Export invariants.
From iris.proofmode Require Import proofmode.
From iris.heap_lang Require Import proofmode notation.
From iris.heap_lang.lib Require Import par.
From iris.base_logic Require Import cancelable_invariants.
From iris.prelude Require Import options.


Section s.

  Context `{!heapGS Σ}.
  Notation iProp := (iProp Σ).

  Lemma ex_4_2 :
    forall P e Q,
      {{{ P }}} e {{{ r, RET r; Q r }}} ->
      forall R, {{{ P ∗ ⌜R⌝ }}} e {{{ r, RET r; Q r ∗ ⌜R⌝ }}}.
  Proof.
    intros P e Q Spec R Q'.
    iIntros "[H1 H2] H3".
    wp_apply (Spec with "H1") as (r) "H4".
    iApply "H3".
    iSplit; done.
  Qed.

  Lemma ex_4_3 :
    {{{ ⌜True⌝ }}}
      (#3 + #4 + #5)
      {{{ r, RET r; ⌜r = #12⌝ }}}.
  Proof.
    iIntros (Q) "H1 H2".
    wp_bind (#3 + #4)%E. (* Not necessary, just used for this exercise. *)
    repeat wp_op.
    iApply "H2".
    done.
  Qed.

  Lemma ex_4_8 :
    forall P (e : expr) (u : val) Q,
    {{{ P }}} e {{{ r, RET r; Q }}} ->
    {{{ P }}} ((Fst (e, u))%V) {{{ r, RET r; Q }}}.
  Proof.
    iIntros (P e u Q Spec Q') "H1 H2".
    wp_bind e.
    wp_apply (Spec with "H1") as (r) "H3".
    wp_pure.
    wp_pure.
    iModIntro.
    iApply "H2".
    done.
  Qed.

  Lemma ex_4_9:
    forall P Q (v : val) (e1 : expr) (e2 : expr),
      {{{ P ∗ ⌜v = #true⌝ }}} e1 {{{ r, RET r; Q }}} ->
      {{{ P ∗ ⌜v = #true⌝ }}} (if: v then e1 else e2)%E {{{ r, RET r; Q }}}.
  Proof using.
    iIntros (P Q v e1 e2 Spec H2) "[H4 H5] H6".
    iDestruct "H5" as "%H3".
    rewrite H3.
    wp_if.
    wp_apply (Spec with "[H4]").
    1: iSplit.
    all: done.
  Qed.

  (* 4.21 *)

  Fixpoint isList (l : val) (xs : list Z) : iProp :=
    match xs with
    |nil => ⌜l = (InjLV #())⌝
    |cons x tl  => ∃ (hd : loc) l', ⌜l = InjRV #hd⌝ ∗ hd ↦ (#x, l') ∗ ▷ isList l' tl
  end.

  Locate expr.

  Definition inc : val :=
    rec: "inc" "x":=
      match: "x" with
        InjL "()" => #()
      | InjR "x2" =>
          let: "h" := Fst !"x2" in
          let: "t" := Snd !"x2" in
          "x2" <- (#1 + "h", "t");;
          "inc" "t"
      end.

  Lemma ex_4_21 :
    forall l xs,
    {{{ isList l xs }}}
      inc l
      {{{ RET #(); isList l (map (Z.add 1) xs) }}}.
  Proof.
    iIntros (l xs Q) "H1 H2".
    iLöb as "Ih" forall (l xs).
    wp_rec.
    destruct xs as [|x xs].
    - iUnfold isList in "H1".
      iDestruct "H1" as "%Heq".
      rewrite Heq.
      wp_match.
      iModIntro. iApply "H2".
      done.
    - iDestruct "H1" as "[%hd [%tl [H1 [H3 H4]]]]".
      iDestruct "H1" as "%Heq".
      rewrite Heq.
      wp_match.
      wp_load.
      wp_pures.
      wp_load.
      wp_pures.
      wp_store.
      iApply ("Ih" with "[H4]").
      + Unshelve. 2: apply xs. iApply "H4".
      + iSimpl in "H2".
        iNext.
        iIntros "H4".
        iApply "H2".
        iFrame.
        done.
  Qed.
End s.

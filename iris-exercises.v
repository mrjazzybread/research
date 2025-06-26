From iris.algebra Require Import frac gmap auth.
From iris.base_logic Require Export invariants.
From iris.proofmode Require Import proofmode.
From iris.heap_lang Require Import proofmode notation.
From iris.heap_lang.lib Require Import par.
From iris.base_logic Require Import cancelable_invariants.
From iris.prelude Require Import options.

From iris.algebra Require Import numbers excl auth gset frac.

Section abql_code.

  (* The ABQL is a variant of a ticket lock which uses an array.

     The lock consists of three things:
     - An array of booleans which contains true at a single index and false at
       all other indices.
     - A natural number, which represents the next available ticket. Tickets are
       increasing and the remainder from dividing the ticket with the length of
       the array gives an index in the array to which the ticket corresponds.
     - The length of the array. The lock can handle at most this many
       simultaneous attempts to acquire the lock. We call this the capacity of
       the lock. *)
  Definition newlock : val :=
    λ: "cap", let: "array" := AllocN "cap" #false in
              ("array" +ₗ #0%nat) <- #true ;; ("array", ref #0, "cap").

  (* wait_loop is called by acquire with a ticket. As mentioned, the ticket
     corresponds to an index in the array. If the array contains true at that
     index we may acquire the lock otherwise we spin. *)
  Definition wait_loop : val :=
    rec: "spin" "lock" "ticket" :=
      let: "array" := Fst (Fst "lock") in (* Get the first element of the triple *)
      let: "idx" := "ticket" `rem` (Snd "lock") in (* Snd "Lock" gets the third element of the triple *)
      if: ! ("array" +ₗ "idx") then #() else ("spin" "lock" "ticket").

  (* To acquire the lock we first take the next ticket using FAA. The wait_loop
     function then spins until the ticket grants access to the lock. *)
  Definition acquire : val :=
    λ: "lock", let: "next" := Snd (Fst "lock") in
               let: "ticket" := FAA "next" #1%nat in
               wait_loop "lock" "ticket" ;;
               "ticket".

  (* To release the lock, the index in the array corresponding to the current
     ticket is set to false and the next index (possibly wrapping around the end
     of the array) is set to true. *)
  Definition release : val :=
    λ: "lock" "o", let: "array" := Fst (Fst "lock") in
                   let: "cap" := Snd "lock" in
                   "array" +ₗ ("o" `rem` "cap") <- #false ;;
                   "array" +ₗ (("o" + #1) `rem` "cap") <- #true.

End abql_code.

Module spec.

  (* Acquiring the lock consists of taking a ticket and spinning on an entry in
     the array. If there are more threads waiting to acquire the lock than there
     are entries in the array, several threads will spin on the same entry in
     the array, and they may both enter their critical section when this entry
     becomes true. Thus, to ensure safety the specification must ensure that
     this can't happen. To this end the specification is that of a ticket lock,
     but extended with _invitations_.

     Invitations are non-duplicable tokens which gives permission to acquire the
     lock. In newlock, when a lock is created with capacity `n` the same amount
     of invitations are created. These are tied to the lock through the ghost
     name γ. acquire_spec consumes one invitaiton and release_spec hands back
     one invitation. Together this ensures that at most `n` threads may
     simultaneously attempt to acquire the lock.

     invitation_split allows the client to split and combine invitations. *)

  Structure abql_spec Σ `{!heapGS Σ} := abql {
    (* Operations *)
    newlock : val;
    acquire : val;
    release : val;
    (* Predicates *)
    is_lock (γ ι κ : gname) (lock : val) (cap : nat) (R : iProp Σ) : iProp Σ;
    locked (γ κ: gname) (o : nat) : iProp Σ;
    invitation (ι : gname) (n : nat) (cap : nat) : iProp Σ;
    (* General properties of the predicates *)
    is_lock_persistent γ ι κ lock cap R : Persistent (is_lock γ ι κ lock cap R);
    locked_timeless γ κ o : Timeless (locked γ κ o);
    locked_exclusive γ κ o o' : locked γ κ o -∗ locked γ κ o' -∗ False;
    invitation_split γ (n m cap : nat) :
      invitation γ (n + m) cap ⊣⊢ invitation γ n cap ∗ invitation γ m cap;
    (* Program specs *)
    newlock_spec (R : iProp Σ) (cap : nat) :
      {{{ R ∗ ⌜0 < cap⌝ }}}
        newlock (#cap)
      {{{ lk γ ι κ, RET lk; (is_lock γ ι κ lk cap R) ∗ invitation ι cap cap }}};
    acquire_spec γ ι κ lk cap R :
      {{{ is_lock γ ι κ lk cap R ∗ invitation ι 1 cap}}}
        acquire lk
      {{{ t, RET #t; locked γ κ t ∗ R }}};
    release_spec γ ι κ lk cap o R :
      {{{ is_lock γ ι κ lk cap R ∗ locked γ κ o ∗ R }}}
        release lk #o
      {{{ RET #(); invitation ι 1 cap }}};
  }.

End spec.

Section algebra.

  (* We create a resource algebra used to represent invitations. The RA can be
     thought of as "addition with an upper bound". The carrier of the resource
     algebra is pairs of natural numbers. The first number represents how many
     invitations we have and the second how many invitations exists in total.

     We want (a, n) ⋅ (b, n) to be equal to (a + b, n). We never combine
     elements (a, n) ⋅ (b, m) where n ≠ m. Hence what happens it that case is
     arbitary, as long the laws for a RA are satisfied. We can not, for instance,
     just disregard the second upper bound as that whould violate commutativity,
     and using `max` would not satisfy the laws for validity. We could use
     agreement, but choose to use `min` instead as it is easier to work with. *)
  Record addb : Type := Addb { addb_proj : nat * min_nat }.

  Canonical Structure sumRAC := leibnizO addb.

  Local Instance addb_op : Op addb := λ a b, Addb (addb_proj a ⋅ addb_proj b).

  (* The definition of validity matches the intuition that if there exists n
     invitations in totoal then one can at most have n invitations. *)
  Local Instance addb_valid : Valid addb :=
    λ a, match a with Addb (x, MinNat n) => x ≤ n end.

  (* Invitations should not be duplicable. *)
  Local Instance addb_pcore : PCore addb := λ _, None.

  (* We need these auxiliary lemmas in the proof below. *)
  Lemma sumRA_op_second a b (n : min_nat) : Addb (a, n) ⋅ Addb (b, n) = Addb (a + b, n).
  Proof. by rewrite /op /addb_op -pair_op idemp_L. Qed.

  (* If (a, n) is valid ghost state then we can conclude that a ≤ n *)
  Lemma sumRA_valid a n : ✓(Addb (a, n)) ↔ a ≤ min_nat_car n.
  Proof. destruct n. split; auto. Qed.

  Definition sumRA_mixin : RAMixin addb.
  Proof.
    split; try apply _; try done.
    - intros ???. rewrite /op /addb_op /=. apply f_equal, assoc, _.
    - intros ??. rewrite /op /addb_op /=. apply f_equal, comm, _.
    - intros [[?[?]]] [[?[?]]]. rewrite 2!sumRA_valid nat_op /=. lia.
  Qed.

  Canonical Structure sumRA := discreteR addb sumRA_mixin.

  Global Instance sumRA_cmra_discrete : CmraDiscrete sumRA.
  Proof. apply discrete_cmra_discrete. Qed.

  Class sumG Σ := SumG { sum_inG :: inG Σ sumRA }.
  Definition sumΣ : gFunctors := #[GFunctor sumRA].

  Global Instance subG_sumΣ {Σ} : subG sumΣ Σ → sumG Σ.
  Proof. solve_inG. Qed.

End algebra.

Section s.

  Context `{!heapGS Σ, !spawnG Σ}.
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
    iApply "H2".
    done.
  Qed.

  Lemma ex_4_9:
    forall P Q (v : val) (e1 : expr) (e2 : expr),
      {{{ P ∗ ⌜v = #true⌝ }}} e1 {{{ r, RET r; Q }}} ->
      {{{ P ∗ ⌜v = #true⌝ }}} (if: v then e1 else e2)%E {{{ r, RET r; Q }}}.
  Proof using.
    iIntros (P Q v e1 e2 Spec H2) "[H4 %H5] H6".
    subst v.
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
      iApply "H2".
      done.
    - iDestruct "H1" as "[%hd [%tl [%H1 [H3 H4]]]]".
      rewrite H1.
      wp_match.
      wp_load.
      wp_pures.
      wp_load.
      wp_pures.
      wp_store.
      iApply ("Ih" with "H4").
      iNext.
      iIntros "H4".
      iApply "H2".
      iFrame.
      done.
  Qed.

  Definition append : val :=
    rec: "append" "l" "l'" :=
      match: "l" with
      InjL "()" => "l'"
      |InjR "x2" =>
         let: "p" := !"x2" in
         let: "r" := "append" (Snd "p") "l'" in
         "x2" <- (Fst "p", "r");;
         InjR ("x2") end.

  Lemma append_sepc :
    forall xs ys l l',
    {{{ isList l xs ∗ isList l' ys }}}
      append l l'
      {{{ r, RET r; isList r (xs ++ ys) }}}.
  Proof using.
    iIntros (xs ys l l' ϕ) "[P1 P2] Q".
    iLöb as "Ih" forall (l xs ϕ).
    wp_lam.
    destruct xs as [|h xs'].
    1: iDestruct "P1" as "%Heq".
    2: iDestruct "P1" as "[%hd [%tl [%Heq [H3 H4]]]]".
    all: rewrite Heq;
      wp_pures.
    2:
      wp_load;
    wp_pures;
    wp_bind (append tl l');
    wp_apply ("Ih" with "H4 P2");
    iIntros (r) "H1";
    wp_pures;
    wp_store;
    wp_pures.
    all:
      iApply "Q";
      iFrame;
      done.
  Qed.

  Definition incl : val := λ: "x", ("x" <- !"x" + #1).

  Local Set Default Proof Using "Type*".

  Lemma ex_8_1 :
    forall l1 (v1 : Z) l2 (v2 : Z),
      {{{ l1 ↦ #v1 ∗ l2 ↦ #v2 }}}
        (incl #l1) ||| (incl #l2)
      {{{ RET (#(), #()); l1 ↦ #(v1 + 1) ∗ l2 ↦ #(v2 + 1) }}}.
  Proof.
    iIntros (l1 v1 l2 v2 ϕ) "[H1 H2] Q".
    unfold incl.
    wp_smart_apply (wp_par with "[H1] [H2]").
    + wp_lam. wp_load. wp_store.
      Unshelve.
      2: apply (fun v => ⌜v = #()⌝ ∗ l1 ↦ #(v1 + 1))%I.
      2: apply (fun v => ⌜v = #()⌝ ∗ l2 ↦ #(v2 + 1))%I.
      iModIntro. iSplit;  done.
    + wp_lam. wp_load. wp_store. iModIntro. iSplit; done.
    + iIntros (r1 r2) "[[%Heq1 H1] [%Heq2 H2]]".
      subst.
      iApply "Q".
      iNext. iFrame.
  Qed.

  Definition linv (l : loc) (n : Z) : iProp := ∃ (m : Z), l ↦ #m ∗ ⌜m >= n⌝%Z.

  Lemma inc_inv :
    forall l n,
      inv nroot (linv l n) -∗
      WP incl #l {{ v, ⌜v = #()⌝ }}.
    iIntros (l n) "#I".
    wp_lam.
    wp_bind (!_)%E.
    iInv "I" as (m) "[H1 #H2]" "Hclose".
    wp_load.
    iMod ("Hclose" with "[H1]") as "_".
    { iExists m. iSplit; done. }
    iModIntro.
    wp_pures.
    iInv "I" as (m') "[H1 _]" "Hclose".
    wp_store.
    iMod ("Hclose" with "[H1]") as "_".
    { iExists (m + 1)%Z. iNext. iSplit.
      + done.
      + iDestruct "H2" as "%H2".
        iPureIntro. lia. }
    iModIntro.
    done.
  Qed.

  Lemma ex_8_5 :
    forall l (n : Z),
      {{{ l ↦ #n }}}
        (incl #l ||| incl #l);; !#l
      {{{ v, RET v; ∃ (m : Z), ⌜#m = v⌝ ∗ ⌜m >= n⌝%Z }}}.
  Proof.
    iIntros (l n ϕ) "I H1".
    iMod (inv_alloc nroot _ (linv l n) with "[I]") as "#I".
    { iExists n. iFrame. iPureIntro. lia. }
    wp_pures.
    wp_apply wp_par as (v1 v2) "_".
    Unshelve.
    4, 5: apply (fun v => ⌜v = #()⌝)%I.
    1, 2: iApply inc_inv; iApply "I".
    iNext.
    wp_pures.
    iInv "I" as (m) "[H2 H3]" "Hclose".
    wp_load.
    iDestruct "H3" as "%H3".
    iApply "H1".
    iExists m.
    iMod ("Hclose" with "[H2]") as "_".
    { iExists m. iFrame. done. }
    done.
  Qed.

End s.

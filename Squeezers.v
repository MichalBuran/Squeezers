Require Import Arith.
Require Import Relations.
Require Import Lia.

Set Implicit Arguments.

Section Simulation.

Variable Sigma : Set.

Record TransitionSystem := { 
  E : Sigma -> Sigma -> Prop ; 
  Init : Sigma -> Prop;
  Good : Sigma -> Prop;
}.

Variable T : TransitionSystem.

Definition bad_not_terminal :=
forall x : Sigma, ~(T.(Good) x) -> (exists (y : Sigma), T.(E) x y).

Definition bad_preserved  :=
forall x y : Sigma,~ (T.(Good) x) -> T.(E) x y -> (~ (T.(Good) y)).



Definition Recidivist :=
  bad_not_terminal  /\ bad_preserved.


Record Poset (X : Set) := { (*Well-founded.*)
  leq : X -> X -> Prop ; 
  base : X -> Prop ; 
  order:order X leq;
  min_subset_base : forall x : X, (forall y : X, leq y x -> (x = y)) -> base x
}. 

Variable X : Set.
Variable P : Poset X.
Definition Wellfounded :=
  forall (Y : X -> Prop), (exists y : X, Y y) ->
    (exists minY : X, Y minY /\ (forall x : X, P.(leq) x minY -> (x = minY \/ ~(Y x)))).


Definition Reachable  (x y : Sigma):=
clos_refl_trans Sigma T.(E) x y
.

Inductive ReachableInTime : Sigma-> Sigma-> nat -> Prop :=
| refl (x: Sigma): ReachableInTime x x 0
| trans_1n (x y z : Sigma)(n: nat) (H1: T.(E) x y)(H2:ReachableInTime y z n) 
  : ReachableInTime x z (S n)
.

Lemma trans_n1 (x y z : Sigma)(n: nat) (H1: T.(E) y z)(H2:ReachableInTime x y n) 
  : ReachableInTime x z (S n).
Proof.
  generalize dependent x.
  generalize dependent y.
  generalize dependent z.
  induction n.
  - intros. inversion H2. subst. econstructor. apply H1. apply refl.
  - intros. inversion H2. subst. specialize (IHn _ _ H1 _ H5).
    eapply trans_1n.
    + eauto.
    + eauto.  
    
Qed.

Lemma reach_in_time_additive: forall (x y z : Sigma) (a b : nat),
 ReachableInTime x y a -> ReachableInTime y z b -> ReachableInTime x z (a+b).
Proof.
  intros.
  generalize dependent z.
  generalize dependent y.
  generalize dependent x.
  generalize dependent b.
  induction a.
  - intros. simpl. inversion H. assumption.
  - intros. inversion H.
     + apply IHa with (x:= y0) in H0.
        apply trans_1n with (y:=y0). assumption. assumption. assumption.
Qed.

Lemma reachable_in_finite_time : forall (x y : Sigma),
Reachable x y <-> exists (n: nat), ReachableInTime x y n.
Proof.
  split.
  - intros.
    induction H.
    + exists 1.
      apply (trans_1n x  H).
      apply refl.
    + exists 0.
      apply refl.
    + destruct IHclos_refl_trans1.
      destruct IHclos_refl_trans2.
      exists (x0 + x1).
      apply (reach_in_time_additive H1 H2).
  - intros [n H].
    induction H.
    + unfold Reachable. apply rt_refl.
    + apply rt_step in H1. 
      unfold Reachable in *.
      apply rt_trans with (y:=y).
      assumption. assumption.

Qed.
      

Inductive FiniteTrace (x: Sigma) : Prop :=
| succ (h: forall y, (T.(E) x y -> FiniteTrace y)): FiniteTrace x
.

Variable rho :  Sigma -> X.

Inductive TSB (A: TransitionSystem) :=
| cons (HG: A.(Good) = T.(Good))(HE: A.(E) = T.(E))
(HI: A.(Init) = (fun x => (T.(Init) x /\ P.(base) ((rho x))))): TSB A.


Structure Squeezer  := { 
 squeeze : Sigma -> Sigma;
 squeeze_rank_reducing : forall (x: Sigma)
, not (P.(base) (rho x)) -> (P.(leq) (rho (squeeze x)) (rho x) /\ 
((rho (squeeze x))  <> (rho x)));
  initial_anchor : forall (x : Sigma), T.(Init) x -> T.(Init) (squeeze x);
  simulation_inducing:
forall (x  : Sigma), exists n m :nat,(n>0) /\ (forall (y: Sigma),
    ReachableInTime x y n ->  ReachableInTime (squeeze x) (squeeze y) m);
  fault_preservation : forall (x : Sigma),
    ~T.(Good) x -> ~(T.(Good) (squeeze x))
}.
Variable S : Squeezer.
  
Definition leads_to_bad (x: Sigma):=
exists y : Sigma, (exists n, ReachableInTime x y n) /\ not( T.(Good) y).

Definition Counterexample (x: Sigma) :=
leads_to_bad x /\ Init T x.
(*
Lemma bad_not_finitetrace (h1:bad_not_terminal)(h2:bad_preserved): forall x,
(~ ( T.(Good) x) -> ~(FiniteTrace x)).
Proof.
  intros.
  unfold not.
  intros.*)

  
  
  
 (* unfold not.
  intros.
  induction H0.
  - apply h1 in H as h3. destruct h3. apply (h2 x0 x1) in H.
    + apply h in H1 as h4. apply H0 in H1 as h5. apply h5. assumption.
    + apply H1.
Qed.*)
(*
Lemma reach_trace : forall x y, FiniteTrace x -> Reachable x y -> FiniteTrace y.
Proof.
Admitted.*)

(*
Lemma counterexample_not_finitetrace (h1:bad_not_terminal)(h2:bad_preserved): forall x,
 leads_to_bad x -> ~(FiniteTrace x).
Proof.
Admitted. 
  unfold not.
  intros.
  destruct H.
  destruct H.
  apply (bad_not_finitetrace h1 h2) in H1.
  apply H1.
  destruct H.
  - destruct H0. apply h. apply H.
  - apply H0.
  - Admitted.*)

Definition sink (y : Sigma) :=
(forall y', T.(E) y y' -> y'= y) /\ T.(E) y y.

Definition bad_sink :=
forall y, (~ (Good T y) ) -> sink y.
  
Lemma mid x y l m (H: sink y):
ReachableInTime x y l -> exists z,
ReachableInTime x z m /\ ReachableInTime z y (l-m). 
Proof.
  generalize dependent m.
  generalize dependent y.
  generalize dependent x.
  induction l.
  - intros. inversion H0. subst. exists y.
    split.
    + induction m.
        * assumption.
        * eapply trans_n1. apply H. auto.
    + simpl. auto.
  - intros. inversion H0; subst; clear H0.
    + destruct m. 
      -- exists x. split.
          ++ constructor.
          ++ simpl. econstructor; eauto.
      --specialize (IHl _ _ H m H5).
        destruct IHl as [z [Hy0z Hzy]].
        exists z. split.
        * econstructor; eauto.
        * simpl. auto.
Qed.

(*
  eapply trans_1n.


  induction m.
  - intros. inversion H. inversion H0. simpl. exists y.
    split. apply refl. apply refl.
  - intros. inversion H0.
    + simpl. exists y. split. assumption. rewrite Nat.sub_diag.
      apply refl.
    + inversion H.
Admitted.*)
  
(*
Lemma strong_induction (Pr : nat -> Prop):
(Pr 0 /\ (forall n, ((forall k, k<n -> Pr k) -> Pr n))) -> (forall n, Pr n).
Proof.
Admitted.*)

Lemma bad_inf_trace (Hbs:bad_sink ): forall (y: Sigma), ~Good T y ->
 forall (n: nat), exists z, ReachableInTime y z n.
Proof.
  intros.
  exists y.
  induction n.
  - constructor.
  - econstructor.
    + apply Hbs. auto.
    + auto.
Qed.



Lemma strong_bad_preserved (Hbs:bad_sink ):forall y z n, ~Good T y -> ReachableInTime y z n -> ~Good T z.
Proof.
  intros.
  apply Hbs in H as Hsink.
  unfold sink in *.
  destruct Hsink as [Hsucc Hr].
  induction H0.
  - auto.
  - apply Hsucc in H1. subst. auto.
Qed.


Lemma leads_to_bad_preserved : forall (x: Sigma) , bad_sink  ->
leads_to_bad  x -> leads_to_bad  (S.(squeeze) x).
Proof.
  unfold leads_to_bad.
  intros x H counter_x.
  destruct counter_x as [y [[l x_to_y] y_bad]].

  assert (forall k l', l' <k -> forall x' y' : Sigma,
bad_sink ->
(ReachableInTime x' y' l' /\ ~ Good T y') ->
exists z' : Sigma,
  (exists o' : nat, ReachableInTime (squeeze S x') z' o') /\ ~ Good T z').
  { induction k.
    - intros l' l'_less_0.
      inversion l'_less_0.
    - intros l' l'_Sk x' y' rec [x'_to_y' y'_bad].
      assert (exists m n : nat,
                         m > 0 /\
                         (forall y'' : Sigma,
                          ReachableInTime x' y'' m ->
                          ReachableInTime (squeeze S x') (squeeze S y'') n)).
      { apply (simulation_inducing S). }
      destruct H0 as [m [n [m_pos H0]]].
      assert (m <= l' \/ l' < m).
      { apply Nat.le_gt_cases. }
      destruct H1.
      + assert (exists z, ReachableInTime x' z m /\ ReachableInTime z y' (l'-m)).
        { eapply mid. auto. auto. }
        destruct H2 as [z [x'_to_z z_to_y']].
        assert ((l' - m) < k).
        { lia. }
        apply (IHk (l' - m) H2 z y' ) in rec.
        destruct rec as [z' [[o' sqz_to_z'] z'_bad]].
        * exists z'.
          split.
          exists (n+o').
          apply H0 in x'_to_z.
          apply (reach_in_time_additive (x'_to_z) sqz_to_z').
          assumption.
        * split. assumption. assumption.
      + assert (exists z, ReachableInTime y' z (m-l')).
        { apply bad_inf_trace. assumption. assumption. }
        destruct H2 as [z y'_to_z].
        exists (squeeze S z).
        split.
        * exists n.
          apply H0.
          assert (m = l' + (m - l')).
          { lia. }
          rewrite H2.
          apply (reach_in_time_additive x'_to_y' y'_to_z).
        * apply fault_preservation.
          apply (strong_bad_preserved H y'_bad y'_to_z). }
  apply H0 with (l':=l)(k:=1+l)(y' :=y).
  - apply Nat.lt_succ_diag_r.
  - assumption.
  - split.
    + assumption.
    + assumption.
Qed.

Lemma one : forall (x: Sigma) , bad_sink  ->
Counterexample  x -> Counterexample  (S.(squeeze) x).
Proof.
  unfold Counterexample.
  intros.
  destruct H0.
  split.
  - apply leads_to_bad_preserved; auto.
  - apply initial_anchor. auto.
Qed.
  

End Simulation.
Section main.
Variable Sigma X : Set. 
Variable rho : Sigma -> X.
Variable T : TransitionSystem Sigma.
Variable P : Poset X.
Definition Safe (T': TransitionSystem Sigma) :=
forall x : Sigma, ~Counterexample T' x.

Definition ImagesOfCounterexamples: (X -> Prop) :=
(fun x => (exists sigma: Sigma, (rho sigma = x)/\Counterexample T sigma)).


Theorem Soundness :forall A, Wellfounded P -> bad_sink T  -> (TSB A) X P rho T-> Safe A -> Safe T.
Proof.
  intros.
  inversion H1. unfold Safe in *. unfold not in *.   
  intros.
  assert (ImagesOfCounterexamples (rho x)).
  { exists x. auto. }
  specialize (H ImagesOfCounterexamples).
  assert (exists y : X, ImagesOfCounterexamples y).
  { exists (rho x). auto. }
  apply H in H5.
  destruct H5 as [ minY [minYinY minYmin]].
  unfold ImagesOfCounterexamples in minYinY.
  destruct minYinY as [ sigma [ Hrhosigma Hcsigma ]].
  specialize (H2 sigma).
  unfold Counterexample in H2.
  apply H2.
  unfold Counterexample in Hcsigma.
  destruct Hcsigma.
  split.
  - unfold leads_to_bad in *. destruct H5. exists x0.
    destruct H5. destruct H5. split.
    + exists x1. assert (forall a b t, ReachableInTime T a b t <-> ReachableInTime A a b t).
      { split.
        - intro. induction H8.
          + apply refl.
          + eapply trans_1n.
            * rewrite <- HE. apply H8.
            * auto.
        - intro. induction H8.
          + apply refl.
          + eapply trans_1n.
            * rewrite HE. apply H8.
            * auto. }
    apply H8. auto.
    + rewrite <- HG. auto.
  - rewrite HI in H6. destruct H6. auto.
Qed.



End Simulation.

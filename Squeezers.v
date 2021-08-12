Require Import Arith.
Require Import Relations.

Set Implicit Arguments.

Section Simulation.

Variable Sigma : Set.

Record TransitionSystem := { (*Really a recidivist Transition System*)
  (* States *)
  E : Sigma -> Sigma -> Prop ; (* Transitions, the last nat is label *)
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

(*Maybe make this a different section*)
Record Poset (X : Set) := { (*Well-founded.*)
  leq : X -> X -> Prop ; 
  base : X -> Prop ; 
  order:order X leq;
  min_subset_base : forall x : X, (forall y : X, leq y x -> (x = y)) -> base x
}. 
Variable X : Set.
Variable P : Poset X.


Definition Reachable  (x y : Sigma):=
clos_refl_trans Sigma T.(E) x y
.

Inductive ReachableInTime : Sigma-> Sigma-> nat -> Prop :=
| refl (x: Sigma): ReachableInTime x x 0
| trans_1n (x y z : Sigma)(n: nat) (H1: T.(E) x y)(H2:ReachableInTime y z n) 
  : ReachableInTime x z (S n)
| trans_n1 (x y z : Sigma)(n: nat) (H1: T.(E) y z)(H2:ReachableInTime x y n) 
  : ReachableInTime x z (S n)
.

Lemma reachable_in_finite_time : forall (x y : Sigma),
Reachable x y <-> exists (n: nat), ReachableInTime x y n.
Proof.
Admitted.

Inductive FiniteTrace (x: Sigma) : Prop :=
| succ (h: forall y, (T.(E) x y -> FiniteTrace y)): FiniteTrace x
.

Variable rho :  Sigma -> X.
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
  
Definition Counterexample (x: Sigma):=
exists y : Sigma, Reachable x y /\ not( T.(Good) y).

Lemma bad_not_finitetrace (h1:bad_not_terminal)(h2:bad_preserved): forall x,
(~ ( T.(Good) x) -> ~(FiniteTrace x)).
Proof.
  unfold not.
  intros.
  induction H0.
  - apply h1 in H as h3. destruct h3. apply (h2 x0 x1) in H.
    + apply h in H1 as h4. apply H0 in H1 as h5. apply h5. assumption.
    + apply H1.
Qed.

Lemma reach_trace : forall x y, FiniteTrace x -> Reachable x y -> FiniteTrace y.
Proof.
Admitted.


Lemma counterexample_not_finitetrace (h1:bad_not_terminal)(h2:bad_preserved): forall x,
 Counterexample x -> ~(FiniteTrace x).
Proof.
  unfold not.
  intros.
  destruct H.
  destruct H.
  apply (bad_not_finitetrace h1 h2) in H1.
  apply H1.
  destruct H.
  - destruct H0. apply h. apply H.
  - apply H0.
  - Admitted.

  
Lemma mid : forall x y m n,
ReachableInTime x y m ->  n <= m -> exists z,
ReachableInTime x z n /\ ReachableInTime z y (m-n).
Proof.
  Admitted.

Lemma strong_induction (Pr : nat -> Prop):
(Pr 0 /\ (forall n, ((forall k, k<n -> Pr k) -> Pr n))) -> (forall n, Pr n).
Proof.
Admitted.

Lemma one : forall (x: Sigma) , Recidivist  ->
Counterexample  x -> Counterexample  (S.(squeeze) x).
Proof.
  unfold Counterexample.
  intros.
  destruct H0.
  destruct H0.
  rewrite reachable_in_finite_time in H0.
  destruct H0.
  generalize dependent x.
  generalize dependent x1.
  apply strong_induction. (*Why does this not do what I want it to do?
  Is it because it doesn't see what follows after (x1 : nat) as having type
  nat -> Prop? How do I fix it?*)






  assert (forall (n : nat), (forall (x : Sigma),
Recidivist ->
(exists y : Sigma, ReachableInTime x y n /\ ~ Good T y) ->
exists y : Sigma, Reachable (squeeze S x) y /\ ~ Good T y)).
  { apply strong_induction (fun n => forall (x : Sigma),
Recidivist ->
(exists y : Sigma, ReachableInTime x y n /\ ~ Good T y) ->
exists y : Sigma, Reachable (squeeze S x) y /\ ~ Good T y))).
    split.


  apply (reachable_in_finite_time).
  intros.
  unfold Counterexample in *.
  destruct H.
  destruct H0 as (w,H0).
  destruct H0.
  apply reachable_in_finite_time in H0.
  destruct H0 as (n,H0).
  assert (exists n m : nat,
                         n > 0 /\
                         (forall y : Sigma,
                          ReachableInTime x0 y n ->
                          ReachableInTime (squeeze S x0) (squeeze S y) m)).
  { apply S.(simulation_inducing). }
  destruct H3.
  destruct H3.
  destruct H3.
  assert ( x1 <= n \/ n < x1).
  { apply Nat.le_gt_cases. }
  destruct H5.
  - assert (exists mid, ReachableInTime x0 mid x1 /\ ReachableInTime mid w (n-x1)).
    { apply mid. apply H0. assumption. }
    destruct H6. destruct H6.
    apply H4 in H6.
    





















  intros.
  unfold Counterexample in *.
  destruct H.
  destruct H0 as (w,H0).
  destruct H0.
  apply reachable_in_finite_time in H0.
  destruct H0 as (n,H0).
  destruct S.
  simpl.
  assert (exists n m : nat,
                         n > 0 /\
                         (forall y : Sigma,
                          ReachableInTime x y n ->
                          ReachableInTime (squeeze0 x) (squeeze0 y) m)).
  { apply simulation_inducing0. }
  destruct H3.
  destruct H3.
  destruct H3.
  assert (forall m k, k<m ->forall x : Sigma,
ReachableInTime x y n ->
(forall y0 : Sigma,
 ReachableInTime x y0 x0 -> ReachableInTime T (squeeze0 x) (squeeze0 y0) x1) ->
exists y0 : Sigma, Reachable T (squeeze0 x) y0 /\ ~ Good T y0).
  {
  induction m. (*redundant*)
  - intros. inversion H5. 
  - intros.
Admitted.

 

(*What follows are futile attempts, which didn't lead anywhere*)


  assert (exists n':nat, n'>n /\ forall z: Sigma, ReachableInTime T x z n' 
    -> Reachable T (squeeze0  x) (squeeze0 z)).
  { induction n.
    - assert (exists n m : nat,
                         n > 0 /\
                         (forall y : Sigma,
                          ReachableInTime T x y n ->
                          ReachableInTime T (squeeze0 x) (squeeze0 y) m)).
      { apply simulation_inducing0. }
      destruct H3.
      exists x0.
      destruct H3.
      destruct H3.
      split. assumption. intros. apply H4 in H5. apply reachable_in_finite_time.
        exists x1. apply H5.
    -
  
      







  generalize dependent H2.
  generalize dependent x.
  generalize dependent y.
  induction n.
  - intros.
    inversion H0. 
    destruct S.
    simpl.
    assert (exists n m : nat,
                         n > 0 /\
                         (forall y : Sigma,
                          ReachableInTime T x y n ->
                          ReachableInTime T (squeeze0 x) (squeeze0 y) m)).
    { apply simulation_inducing0. }
    destruct H5.
    destruct H5.
    destruct H5.
    assert (forall n:nat, exists (z: Sigma), ReachableInTime T x z n /\ ~ Good T z).
    { induction n.
      - exists y. split. apply H0. apply H2.
      - destruct IHn. destruct H7. assert (~ Good T x3). { apply H8. } apply H in H8. destruct H8. exists x4. split.
        + apply (trans_n1 (y := x3)). apply H8. apply H7.
        + apply (H1 x3 x4) in H9. apply H9. apply H8. }
    assert (exists z : Sigma, ReachableInTime T x z x1 /\ ~ Good T z).
    { apply H7. }
    destruct H8. destruct H8. exists (squeeze0 x3). split.
    + apply reachable_in_finite_time. exists x2. rewrite <- H4. apply H6.
      apply H8.
    + apply fault_preservation0. apply H9.
  - intros.
  




forall M : nat, exists x2:Sigma, exists m:nat, ReachableInTime T x x2 m /\
            m>M /\ ~ Good T x2).
  { intros. assert (exists n m : nat,
    n <> 0 /\
    (forall y : Sigma,
     ReachableInTime T x y n -> ReachableInTime T (squeeze0 x) (squeeze0 y) m)).
    { apply simulation_inducing0. }
    destruct H3.
    destruct H3.
    destruct H3.



induction M.
    - destruct x1.
      + assert (~ Good T x0). {apply H2. } apply H in H2. destruct H2. exists x1. exists 1. split.
        * inversion H0.
          -- rewrite H5 in H0. assert (ReachableInTime T x1 x1 0).
          { apply refl. }
          apply (trans_1n x0  H2 H6).
          -- rewrite plus_comm in H4. discriminate H4.
        * split.
          -- apply gt_Sn_O.
          -- unfold not. intros. apply fault_preservation0  in H4.

  assert (exists f f':nat->nat, exists n : nat, exists  g :nat ->Sigma,
    g 0 = x /\ g n = x0 /\ forall n, ReachableInTime T (g n) (g (n+1)) (f n)
    /\ forall n, ReachableInTime T (squeeze0 (g n)) (squeeze0 (g (n+1))) (f' n)).
  { 


  induction x1.
  - inversion H. exists (squeeze0 x0). split.
    + unfold Reachable in *. apply rt_refl.
    + intro. apply fault_preservation0 in H3. contradiction.
    + rewrite plus_comm in H1. discriminate H1.
  -





apply clos_rt_rt1n in H.
induction H.
- exists (S.(squeeze) x).
  destruct S.
  simpl.
  split.
  + apply rt_refl.
  + intro. apply fault_preservation0 in H. contradiction.
- apply IHclos_refl_trans_1n in H0.
  destruct H0.
  destruct H0.
  assert (Reachable T (squeeze S x) x0). 
  { destruct S.
    simpl.
    
(* Old Proof
intros.
unfold Counterexample in *.
destruct H.
destruct H.
apply clos_rt_rt1n in H.
induction H.
- exists (S.(squeeze) x).
  destruct S.
  simpl.
  split.
  + apply rt_refl.
  + intro. apply fault_preservation0 in H. contradiction.
- apply IHclos_refl_trans_1n in H0.
  destruct H0.
  destruct H0.
  assert (Reachable T (squeeze S x) x0). 
  { destruct (S.(one_one_simulation_inducing) x y H).
    + rewrite H3. apply H0.
    + apply rt_trans with (y := squeeze S y). apply rt_step. assumption.
      apply H0. }
  exists (x0).
  split. apply H3. apply H2.*)
Qed.

  

(*
induction H.
- exists (S.(squeeze) y).
  destruct S. simpl. split.
  + destruct (one_one_simulation_inducing0 x y H).
    * rewrite H1. apply rt_refl.
    * constructor. assumption.
  + unfold not. intros. apply fault_preservation0 in H1. contradiction.
- exists (S.(squeeze) x).
  destruct S.
  simpl.
  split.
  + apply rt_refl.
  + intro. apply fault_preservation0 in H. contradiction.
- 
  



intros.
induction H. 
- destruct S. (*Is there a way how to destruct S only in the hypothesis?*)
 apply initial_anchor0 in H. apply fault_preservation0  in H0.
  apply Init_Bad.
  + apply H.
  + apply H0.
- destruct S. apply weak_simulation_inducing0 in H. (*Now I'd like to destruct H to deal
with the cases when squeeze x = squeeze y and the case when there is a transition from
squeeze x to squeeze y. In the first case I can just rewrite Counterexample T (squeeze S y)
as Counterexample T (squeeze S x). In the second I can succ_Counterexample.
Unfortunately, I can't destruct H and I'm not sure why. I'm just trying to do a case
analysis on 'or'. Is it illegal to split (Prop or Prop) into two cases? Is this for some
reason only allowed with booleans?*)
  rewrite (orb_equiv_or (squeeze0 x = squeeze0 y) (exists w : nat, E T (squeeze0 x) (squeeze0 y) w)) in H.
  (*Destructing H again doesn't do what I want it to do.*)
  *)


End Simulation.




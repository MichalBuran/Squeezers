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
    + assert (ReachableInTime y0 z (S b)).
      { apply trans_1n with (y:=y). assumption. assumption. }
      rewrite Nat.add_succ_comm.
      apply IHa with (y := y0).
      assumption. assumption.
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
    + apply rt_step in H1.
      unfold Reachable in *.
      apply rt_trans with (y := y).
      assumption. assumption.
Qed.
      

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
exists y : Sigma, (exists n, ReachableInTime x y n) /\ not( T.(Good) y).
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
 Counterexample x -> ~(FiniteTrace x).
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

  
Lemma mid : forall x y m n,
ReachableInTime x y m ->  n <= m -> exists z,
ReachableInTime x z n /\ ReachableInTime z y (m-n).
Proof.
  intros x y m n.
  generalize dependent n.
  generalize dependent y.
  generalize dependent x.
  induction m.
  - intros. inversion H. inversion H0. simpl. exists y.
    split. apply refl. apply refl.
  - intros. inversion H0.
    + simpl. exists y. split. assumption. rewrite Nat.sub_diag.
      apply refl.
    + inversion H.
Admitted.
  

Lemma strong_induction (Pr : nat -> Prop):
(Pr 0 /\ (forall n, ((forall k, k<n -> Pr k) -> Pr n))) -> (forall n, Pr n).
Proof.
Admitted.

Lemma ineq : forall a b c : nat, a <1+ b -> c >0 -> a-c < b.
Proof.
Admitted.

Lemma bad_inf_trace : forall (y: Sigma), ~Good T y ->
 forall (n: nat), exists z, ReachableInTime y z n.
Proof.
Admitted.



Lemma alg1 : forall  m n, m = n + (m - n).
Proof.
Admitted.

Lemma strong_bad_preserved :forall y z n, ~Good T y -> ReachableInTime y z n -> ~Good T z.
Proof.
Admitted.

Lemma one : forall (x: Sigma) , Recidivist  ->
Counterexample  x -> Counterexample  (S.(squeeze) x).
Proof.
  unfold Counterexample.
  intros x H counter_x.
  destruct counter_x as [y [[l x_to_y] y_bad]].

  assert (forall k l', l' <k -> forall x' y' : Sigma,
Recidivist ->
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
        { apply (mid x'_to_y' H1). }
        destruct H2 as [z [x'_to_z z_to_y']].
        assert ((l' - m) < k).
        { apply (ineq l'_Sk m_pos). }
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
        { apply bad_inf_trace. assumption. }
        destruct H2 as [z y'_to_z].
        exists (squeeze S z).
        split.
        * exists n.
          apply H0.
          assert (m = l' + (m - l')).
          { apply alg1. }
          rewrite H2.
          apply (reach_in_time_additive x'_to_y' y'_to_z).
        * apply fault_preservation.
          apply (strong_bad_preserved y'_bad y'_to_z). }
  apply H0 with (l':=l)(k:=1+l)(y' :=y).
  - apply Nat.lt_succ_diag_r.
  - assumption.
  - split.
    + assumption.
    + assumption.
Qed.
    (*
  intros.
  induction k.
  - inversion H2.
  - destruct S.
    simpl in *.
    assert (exists n m : nat,
                         n > 0 /\
                         (forall y : Sigma,
                          ReachableInTime x3 y n ->
                          ReachableInTime (squeeze0 x3) (squeeze0 y) m)). 
    { apply simulation_inducing0. }
    destruct H5.
    destruct H4.
    destruct H4.
    destruct H4.
    assert (x4 <= x6 \/ x6 < x4).
    { apply Nat.le_gt_cases. }
    destruct H7.
    + assert (exists z, ReachableInTime x3 z x4 /\ ReachableInTime z x5 (x6-x4)).
      { apply mid. assumption. assumption. }
      destruct H8.
      destruct H8.
      assert (x6 - x4 < k).
      { 
       
    
      
  apply H2.
  destruct H2.
  

  
  generalize dependent x.
  generalize dependent x1.
  intros.
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

*)
End Simulation.




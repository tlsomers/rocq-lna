Require Export Reals.
Require Export LnA.Lra.

Require Import Classical.

(* ----------- simple tactics ----------- *)
Tactic Notation "con_i" :=
  match goal with
  | |- _ /\ _ => split
  end ||
  fail "(the goal is not a conjunction)".

Tactic Notation "con_e1" constr(R) :=
  match goal with
  | |- ?G =>  refine (and_ind (fun (left : G) (_ : R) => left) (_ : G /\ R))
  end.

Tactic Notation "con_e2" constr(L) :=
  match goal with
  | |- ?G => refine (and_ind (fun (_ : L) (right : G) => right) (_ : L /\ G))
  end.

Tactic Notation "dis_i1" :=
  match goal with
  | |- _ \/ _ => left
  end ||
  fail "(the goal is not a disjunction)".

Tactic Notation "dis_i2" :=
  match goal with
  | |- _ \/ _ => right
  end ||
  fail "(the goal is not a disjunction)".

Tactic Notation "dis_e" constr(X) ident(H1) ident(H2) :=
  lazymatch X with
  | ( _ \/ _ ) =>
   let x := fresh "H" in
   assert X as [x|x]; [idtac
     |first [rename x into H1|fail 1 "(the label" H1 "already exists)"]
     |first [rename x into H2|fail 1 "(the label" H2 "already exists)"]]
  | _ => fail "(the argument is not a disjunction)"
  end.

(* The [?Q] makes sure that the conclusion does not depend on the premise.
   That is, it makes sure it is really an implication, not a forall. *)
Tactic Notation "imp_i" ident(X) :=
  lazymatch goal with
  | |- _ -> ?Q => intro X
  | |- _ => fail "(the goal is not an implication)"
  end.

Tactic Notation "imp_e" constr(X) := cut X.

(* Using [type of A] we make sure that we don't quantify over a proposition.
   That is, it makes sure it is really a forall, not an implication. *)
Tactic Notation "all_i" ident(X) :=
  lazymatch goal with
  | |- forall _ : ?A, _ => 
     lazymatch type of A with
     | Prop => fail "(the goal is not a universal quantification)"
     | _ => first [intro X|fail 1 "(the label" X "already exists)"]
     end
  | _ => fail "(the goal is not a universal quantification)"
  end.

Tactic Notation "all_e" constr(X) constr(A) :=
  lazymatch X with
  | forall _ : _ , _ => first
     [refine ((_ : X) A)
     |let G := match goal with |- ?G => G end in
      fail 1 "(instantiating" X "with" A " does not match the goal" G ")"]
  | _ => fail "(the argument is not a universal quantification)"
  end.

Tactic Notation "eqv_i" :=
  match goal with
  | |- _ <-> _ => split
  end ||
  fail "(the goal is not an equivalence)".

Tactic Notation "eqv_e1" :=
  match goal with
  | |- (?B -> ?A) => refine (and_ind (fun (_ : A -> B) (y : B -> A) => y) (_ : A <-> B))
  end ||
  fail "(the goal is not an implication)".

Tactic Notation "eqv_e2" :=
  match goal with
  | |- (?A -> ?B) => refine (and_ind (fun (x : A -> B) (_ : B -> A) => x) (_ : A <-> B))
  end ||
  fail "(the goal is not an implication)".

Tactic Notation "iff_i" ident(H1) ident(H2) :=
  match goal with
  | |- _ <-> _ =>
  split ; [ (imp_i H1) | (imp_i H2) ]
  end ||
  fail "(the goal is not a bi-implication)".

Tactic Notation "iff_e1" constr(R) :=
  match goal with
  | |- ?L => cut R; [ refine (and_ind (fun (_ : L -> R) (y : R -> L) => y) (_ : L <-> R)) | idtac ]
  end.

Tactic Notation "iff_e2" constr(L) :=
  match goal with
  | |- ?R => cut L ; [ refine (and_ind (fun (x : L -> R) (_ : R -> L) => x) (_ : L <-> R)) | idtac ]
  end.

Tactic Notation "neg_e" constr(X) := absurd X.

Tactic Notation "fls_e" := apply False_ind.

Tactic Notation "LEM" :=
  match goal with
  | |- ?H \/ ~ ?H => apply classic
  end ||
  fail "(the goal is not of the form A \/ ~A)".

Tactic Notation "exi_i" constr(X) :=
  lazymatch goal with
  | |- exists x : ?A , _ => first
     [exists X
     |let T := type of X in
      fail 1 "(the type" T "of" X "does not match the type" A " of the quantifier)"
     |fail 1 "(the argument" X "is not a valid term)"]
  | |- _ => fail "(the goal is not an existential quantification)"
  end.

Tactic Notation "exi_e" constr(X) ident(a) ident(H) :=
  lazymatch X with
  | ex _ =>
     refine ((fun x y => ex_ind y (x : X)) _ _); [idtac|
       first [intros a|fail 1 "(the label" a "already exists)"];
       first [intros H|fail 1 "(the label" H "already exists)"]]
  | _ => fail "(the argument is not an existential quantification)"
  end.

Tactic Notation "hyp" constr(X) := exact X. (*assumption.*)

Tactic Notation "neg_i" constr(X) ident(Y) := 
  match goal with
  | |- ~ _ => intro Y; absurd X
  end ||
fail "(the goal is not a negation)".

Tactic Notation "neg_e'" constr(X) ident(Y) := 
  match goal with
  | |- ?H => apply (NNPP H); intro Y; absurd X
  end.

Tactic Notation "replace" constr(x) "with" constr(y) :=
  let H := fresh in assert (x = y) as H; [|rewrite H]. 

(* ------------ intervals ------------ *)
Definition in_cc (a b c : R) := (b <= a)%R /\ (a <= c)%R.
Definition in_co (a b c : R) := (b <= a)%R /\ (a < c)%R.
Definition in_oc (a b c : R) := (b < a)%R /\ (a <= c)%R.
Definition in_oo (a b c : R) := (b < a)%R /\ (a < c)%R.
Definition in_ccZ (a b c : Z) := (b <= a)%Z /\ (a <= c)%Z.
Definition in_coZ (a b c : Z) := (b <= a)%Z /\ (a < c)%Z.
Definition in_ocZ (a b c : Z) := (b < a)%Z /\ (a <= c)%Z.
Definition in_ooZ (a b c : Z) := (b < a)%Z /\ (a < c)%Z.

Notation "a 'in' [ b , c ]" := (in_cc a b c) (at level 70) : R_scope.
Notation "a 'in' [ b , c )" := (in_co a b c) (at level 70) : R_scope.
Notation "a 'in' ( b , c ]" := (in_oc a b c) (at level 70) : R_scope.
Notation "a 'in' ( b , c )" := (in_oo a b c) (at level 70) : R_scope.
Notation "a 'in' [ b , c ]" := (in_ccZ a b c) (at level 70) : Z_scope.
Notation "a 'in' [ b , c )" := (in_coZ a b c) (at level 70) : Z_scope.
Notation "a 'in' ( b , c ]" := (in_ocZ a b c) (at level 70) : Z_scope.
Notation "a 'in' ( b , c )" := (in_ooZ a b c) (at level 70) : Z_scope.

Tactic Notation "interval" := 
  first [progress (
    try unfold in_cc ; 
    try unfold in_co ;
    try unfold in_oc ;
    try unfold in_oo ;
    try unfold in_ccZ ;
    try unfold in_coZ ;
    try unfold in_ocZ ;
    try unfold in_ooZ ;
    try unfold in_ccZ)|
  fail 1 "(the goal is not an interval)"].

(* ------- lin_solve using lra ---------- *)

(*
  fails if the given term is not a singleton linear equation
  examples of singleton linear equations:
    7 > x
    t + 10 <> t1
    3 = 5
  so the following example terms will fail:
    3 = 5 /\ 7 > x
    forall x:R, x <> x + 3
*)
Tactic Notation "is_singleton_eq" constr(X) :=
lazymatch X with
  | (?LHS = ?RHS) => idtac
  | (Rle ?LHS ?RHS) => idtac
  | (Rge ?LHS ?RHS) => idtac
  | (Rlt ?LHS ?RHS) => idtac
  | (Rgt ?LHS ?RHS) => idtac
  | ?LHS <> ?RHS => idtac
  | _ => fail "(argument is not a singleton equation)"
end
.

(*  
  Removes all hypotheses that are not singleton linear equations
  eg:
    H0: foo x
    H1: x > 0 /\ x < 10
    H2: x > 0
    H3: x < 10
  ----------------------
    x < 100
  becomes:
    H2: x > 0
    H3: x < 10
  ----------------------
    x < 100
*)
Tactic Notation "lin_solve_clear_tactic" := 
repeat (
  match goal with 
  | [ X: ?P |- _ ] => try (is_singleton_eq P; revert X); (clear X)
  end); 
intros.

(*  
  Solves simple systems of linear equations, 
  where only singleton equations are accepted in the goal
  and only hypotheses with singleton equations are used to prove this
*)
Tactic Notation "lin_solve" :=
  lazymatch goal with
      | [ |- ?P ] => first [
          is_singleton_eq P
          | fail "(goal is not a single linear equation)"
      ];
      lin_solve_clear_tactic;
      try lraold; 
      fail "(cannot solve this system)"
  end.

(* --------- curry_assumptions ---------- *)

Ltac curry_assumptions_go :=
   lazymatch goal with
   | |- _ /\ _ -> _ =>
       let H1 := fresh in
       let H2 := fresh in
       intros [H1 H2]; revert H2; curry_assumptions_go; revert H1
   | |- _ => idtac
   end.

Tactic Notation "curry_assumptions" :=
   lazymatch goal with
   | |- _ /\ _ -> _ => curry_assumptions_go
   | |- _ => fail "(the goal is not of the proper form)"
   end.

Tactic Notation "test" := idtac.

Open Scope R_scope.

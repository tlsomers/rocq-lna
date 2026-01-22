Require Export LnA.KripkeLA.

Inductive label: Set :=
  i: label.

Inductive level: Set :=
 nil: level 
|cons: label -> level -> level.

Infix " :: " := cons ( at level 60 , right associativity ).

Parameter Ass: level -> formula -> Prop.

Inductive Provable: level -> formula -> Prop :=
 truth: forall (n: level), (Provable n Top)
|ass: forall (phi: formula) (n: level),
  (Ass n phi) -> (Provable n phi)
|andI: forall (phi1 psi2: formula) (n: level),
  (Provable n phi1) -> (Provable n psi2) ->
  (Provable n (And phi1 psi2))
|andE1: forall (phi1 phi2: formula) (n: level),
  (Provable n (And phi1 phi2)) -> (Provable n phi1)
|andE2: forall (phi1 phi2: formula) (n: level),
  (Provable n (And phi1 phi2)) -> (Provable n phi2)
|orI1: forall (phi1 phi2: formula) (n: level),
  (Provable n phi1) -> (Provable n (Or phi1 phi2))
|orI2: forall (phi1 phi2: formula) (n: level),
  (Provable n phi2) -> (Provable n (Or phi1 phi2))
|orE: forall (phi1 phi2 psi: formula) (n: level),
  (Provable n (Or phi1 phi2)) ->
  ((Ass n phi1) -> (Provable n psi)) ->
  ((Ass n phi2) -> (Provable n psi)) -> (Provable n psi)
|impI: forall (phi1 phi2: formula) (n: level),
  ((Ass n phi1) -> (Provable n phi2)) ->
  (Provable n (Imp phi1 phi2))
|biimpI: forall (phi1 phi2: formula) (n: level),
  ((Ass n phi1) -> (Provable n phi2)) ->
  ((Ass n phi2) -> (Provable n phi1)) ->
  (Provable n (BiImp phi1 phi2))
|impE: forall (phi1 phi2: formula) (n: level),
  (Provable n (Imp phi1 phi2)) ->
  (Provable n phi1) -> (Provable n phi2)
|biimpE1: forall (phi1 phi2: formula) (n: level),
  (Provable n (BiImp phi1 phi2)) ->
  (Provable n phi2) -> (Provable n phi1)
|biimpE2: forall (phi1 phi2: formula) (n: level),
  (Provable n (BiImp phi1 phi2)) ->
  (Provable n phi1) -> (Provable n phi2)
|negE: forall (phi psi: formula) (n: level),
  ((Provable n (Not psi))) ->
  ((Provable n (psi))) -> (Provable n phi)
|negI: forall (phi psi: formula) (n: level),
  ((Ass n phi) ->(Provable n (Not psi))) ->
  ((Ass n phi) -> (Provable n (psi))) -> (Provable n (Not phi))
|negEstar: forall (phi psi: formula) (n: level),
  ((Ass n (Not phi)) ->(Provable n (Not psi))) ->
  ((Ass n (Not phi)) -> (Provable n (psi))) -> (Provable n phi)
|notI: forall (phi: formula) (n: level),
  ((Ass n phi) -> (Provable n Bottom)) ->
  (Provable n (Not phi))
|notE: forall (phi: formula) (n: level),
  (Provable n phi) ->
  (Provable n (Not phi)) -> (Provable n Bottom)
|botE: forall (phi: formula) (n: level),
  (Provable n Bottom) -> (Provable n phi)
|notnotE: forall (phi: formula) (n: level),
  (Provable n (Not (Not phi))) -> (Provable n phi)
|boxE: forall (phi: formula) (n: level) l n',
  (n = cons l n') -> (* there must be a box *)
  (Provable n' (Box phi)) -> (Provable n phi)
|boxI: forall (phi: formula) (n: level),
  (Provable (cons i n) phi) -> (Provable n (Box phi))
|t: forall (phi: formula) (n: level),
  (Provable n (Box phi)) -> (Provable n phi)
|four: forall (phi: formula) (n: level),
  (Provable n (Box phi)) -> (Provable n (Box (Box phi)))
|five: forall (phi: formula) (n: level),
  (Provable n (Not (Box phi))) ->
  (Provable n (Box (Not (Box phi)))).

Notation "'[' n ']'  '|-'  phi ":= (Provable n phi) (at level 60). 
Notation "'[' n ']'  ':'  phi ":= (Ass n phi) (at level 60). 
(* 
Notation "'[]' phi" := (Box phi) (at level 60).
Notation "'<>' phi" := (Diamond phi) (at level 60). *)
Ltac Truth := apply truth.
(* Ltac hyp_old n H :=
apply ass_at with n;
  (unfold EqLevel; unfold Remove_o; reflexivity) || (exact H)
. *)

Ltac hyp H :=
  eapply ass; exact H.

Ltac all_i X := intro X.
Ltac exi_i X := exists X.
Ltac con_i := apply andI.
Ltac con_e1 L := apply andE1 with (phi2 := L).
Ltac con_e2 R := apply andE2 with (phi1 := R).
Ltac dis_i1 := apply orI1.
Ltac dis_i2 := apply orI2.
(* Ltac dis_e L R H1 H2 := apply orE with (phi1 := L) (phi2 := R) ;
  [ |intro H1|intro H2]. *)

Ltac dis_e X H1 H2 :=
  match X with
  | ( ?L \/_ ?R) => apply orE with (phi1 := L) (phi2 := R) ;
    [ |intro H1|intro H2]
  end.


Ltac imp_i H := apply impI; intro H.
Ltac imp_e P := apply (impE P).
Ltac iff_i H1 H2 := apply biimpI; [intro H1 | intro H2].
Ltac iff_e1 P := apply biimpE1 with (phi2 := P).
Ltac iff_e2 P := apply biimpE2 with (phi1 := P).
Ltac neg_e P := apply negE with (psi := P).
Ltac neg_i P H := apply negI with (psi := P); intro H.
Ltac neg_e' P H := apply negEstar with (psi := P); intro H.


Ltac box_e := eapply boxE; [reflexivity|].
Ltac box_i := apply boxI.

Ltac Assumed := (apply ass; assumption) || assumption.

Ltac AndIntro := apply andI.
Ltac AndElim1 L := apply andE1 with (phi2 := L). 
Ltac AndElim2 R := apply andE2 with (phi1 := R). 

Ltac OrIntro1 := apply orI1.
Ltac OrIntro2 := apply orI2.
Ltac OrElim L R := apply orE with (phi1 := L) (phi2 := R).
Ltac ImpIntro := apply impI; intro.
Ltac ImpElim P := apply (impE P).
Ltac NotIntro := apply notI; intro.
Ltac NotElim P := apply (notE P).
Ltac BottomElim := apply botE.
Ltac NotNotElim := apply notnotE.
Ltac BoxElim := apply boxE; [reflexivity|].
Ltac BoxIntro := apply boxI.
Ltac replDiamond P := replace (Diamond P) with (Not (Box (Not P)));
  try symmetry; try apply diamond_to_box. 
Ltac replBox P := replace (Box P) with (Not (Diamond (Not P)));
  try symmetry; try apply box_to_diamond. 


Ltac T := apply t.
Ltac Four := apply four.
Ltac Five := apply five.

Lemma LawOfExcludedMiddle:
forall (phi: formula) (n: level),
  (Provable n (Or phi (Not phi))).
Proof.
intros.
neg_e' ((~_ phi)) H.

neg_i (phi \/_ ~_ phi) H1.
hyp H.
dis_i2.

hyp H1.
neg_i (phi \/_ ~_ phi) H1.
hyp H.
dis_i1.

hyp H1.

Qed.

Ltac LEM := apply LawOfExcludedMiddle.

Section EnigmeDesChapeaux.


(* QUELQUES DÉFINITIONS *)

Inductive couleurChapeau : Set := blanc | noir.
Inductive configuration : Set := config : couleurChapeau -> couleurChapeau -> couleurChapeau -> configuration.

Definition chapeauAlbert : configuration -> couleurChapeau := fun c => match c with config couleur _ _ => couleur end.
Definition chapeauMarie : configuration -> couleurChapeau := fun c => match c with config _ couleur _ => couleur end.
Definition chapeauSophie : configuration -> couleurChapeau := fun c => match c with config _ _ couleur => couleur end.


(* L'un des chapeaux est forcément noir puisqu'il n'y a que deux chapeaux blancs et que nous avons trois personnages. D'où l'hypothèse générale que nous faisons pour toute configuration de chapeaux. *)

Hypothesis configurationValide : forall c : configuration, chapeauAlbert c = noir \/ chapeauMarie c = noir \/ chapeauSophie c = noir.

(* Pour ceux qui en doutent : 2 < 3. *)

Require Import Arith.
Goal 2 < 3.
Proof.
  apply le_lt_n_Sm.
  apply le_n.
Qed.


(* LEMMES D'ÉCHAUFFEMENT *)

(* Un chapeau a forcément une couleur. *)

Goal forall couleur : couleurChapeau, (couleur = noir) \/ (couleur = blanc).
Proof.
  intro c.
  destruct c.
  right. reflexivity.
  left. reflexivity.
Qed.

(* Si un chapeau n'est pas de couleur blanche, c'est qu'il est de couleur noire. Et réciproquement : s'il est de couleur noire, c'est qu'il n'est pas de couleur blanche ! *)

Lemma nonBlancEstNoir : forall couleur : couleurChapeau, ~(couleur = blanc) <-> (couleur = noir).
Proof.
  intro c. split.
- intro H.
  destruct c.
  destruct H. reflexivity.
  reflexivity.
- intro H.
  destruct c.
  discriminate H.
  discriminate.
Qed.

(* Par voie de conséquence, un chapeau ne pourra donc jamais être noir et blanc en même temps... *)

Lemma noirOUblanc : forall c : couleurChapeau, c = noir /\ c = blanc -> False.
Proof.
  intros c H.
  destruct H as [H1 H2].
  apply (nonBlancEstNoir c).
  exact H1. exact H2.
Qed.


(* ESSAYONS DE COMPRENDRE POURQUOI SOPHIE RÉUSSIT À DEVINER LA COULEUR DE SON CHAPEAU *)


(* Puisque les chapeaux de Marie et Sophie sont forcément de couleur noire ou blanche, Albert se retrouve donc face à l'une des quatre éventualités suivantes :
  cas 1 : Marie a un chapeau blanc et Sophie a un chapeau blanc
  cas 2 : Marie a un chapeau noir et Sophie a un chapeau blanc
  cas 3 : Marie a un chapeau blanc et Sophie a un chapeau noir
  cas 4 : Marie a un chapeau noir et Sophie a un chapeau noir
*)

Lemma AlbertSait : forall c : configuration, chapeauMarie c = blanc /\ chapeauSophie c = blanc -> chapeauAlbert c = noir.
Proof.
  intros c H.
  destruct H as [H1, H2].
  destruct (configurationValide c).
  exact H.
  destruct H.
  destruct (noirOUblanc (chapeauMarie c)).
  apply (conj H H1).
  destruct (noirOUblanc (chapeauSophie c)).
  apply (conj H H2).
Qed.


(* Puisqu'Albert est indécis, c'est qu'il n'est pas en mesure d'appliquer le lemme précédent. Autrement dit, Albert qui a une très bonne vue ne dispose pas d'une preuve que le chapeau de Marie est blanc en même temps que celui de Sophie est blanc également. Sinon, en posant
  P = chapeauMarie c = blanc /\ chapeauSophie c = blanc
  Q = chapeauAlbert c = noir
Albert aurait appliqué le célèbre modus ponens pour en déduire que son chapeau était noir : *)

Lemma modus_ponens : forall P Q : Prop, P -> (P -> Q) -> Q.
Proof.
  intros P Q p pq.
  apply pq. exact p.
Qed.

(* Le cas 1 "Marie a un chapeau blanc et Sophie a un chapeau blanc" est donc exclu. Dans les trois autres cas, l'un des deux personnages féminins au moins a un chapeau noir. Nous dirons donc qu'Albert est indécis dès que Marie ou Sophie (ou les deux) porte un chapeau noir. *)

Definition AlbertIndecis (c : configuration) : Prop := chapeauMarie c = noir \/ chapeauSophie c = noir.

Lemma MarieSait : forall c : configuration, (AlbertIndecis c) /\ (chapeauSophie c = blanc) -> chapeauMarie c = noir.
Proof.
  intros c H.
  destruct H as [H1, H2].
  destruct H1.
  exact H.
  destruct (noirOUblanc (chapeauSophie c)).
  apply (conj H H2).
Qed.


(* Même raisonnement que pour Albert, si Marie n'est pas en mesure d'appliquer le lemme précédent et donc de deviner la couleur de son propre chapeau, c'est qu'elle ne dispose pas à la fois d'une preuve qu'Albert est indécis et que Sophie a un chapeau blanc. Or Marie, qui n'est pas sourde, sait qu'Albert est indécis puisque ce dernier l'a dit haut et fort. C'est donc que Marie ne sait pas que le chapeau de Sophie est blanc. Mais Marie a elle aussi une très bonne vue et voit bien la couleur du chapeau de Sophie ; d'après le lemme nonBlancEstNoir, le chapeau de Sophie est donc noir. *)

Definition MarieIndecise (c : configuration) : Prop := chapeauSophie c = noir.

Theorem SophieTrouve : forall c : configuration, MarieIndecise c -> chapeauSophie c = noir.
Proof.
  trivial.
Qed.

End EnigmeDesChapeaux.

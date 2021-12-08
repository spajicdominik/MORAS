Set Implicit Arguments.
Require Import Setoid.
Require Import Omega.
Require Import Bool.

(* 1 a *)
Goal forall(x y : bool) ,
orb (orb (negb (andb x y)) (andb (negb x) y)) (andb (negb x) (negb y)) = negb (andb x y).
Proof.
  destruct x. destruct y.
   - simpl. reflexivity.
   - simpl. reflexivity.
  - destruct y.
    -- simpl. reflexivity.
    -- simpl. reflexivity.
Qed.

(* 1 b *)
Goal forall (x y z : bool),
andb (andb (negb (andb (andb (negb x) y) (negb z))) (negb (andb (andb x y) z))) (andb (andb x (negb y)) (negb z)) 
= andb (orb (negb y) (xorb x z)) (andb (andb x (negb y)) (negb z)).
Proof.
destruct x. destruct y. destruct z.
 - simpl. reflexivity.
 - simpl. reflexivity.
- destruct z.
  -- simpl. reflexivity.
  -- simpl. reflexivity.
- destruct y. destruct z.
  -- simpl. reflexivity.
  -- simpl. reflexivity.
-- destruct z.
  --- simpl. reflexivity.
  --- simpl. reflexivity.
Qed.
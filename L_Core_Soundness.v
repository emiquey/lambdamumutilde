(***************************************************************************
* Safety for Simply Typed Lambda Calculus (CBV) - Proofs                   *
* Brian Aydemir & Arthur Chargueraud, July 2007                            *
***************************************************************************)

Set Implicit Arguments.
Require Import LibLN 
  L_Core_Definitions 
  L_Core_Infrastructure.


(* ********************************************************************** *)
(** * Proofs *)

(** Typing is preserved by weakening. *)

Require Import Coq.Program.Equality.
Scheme typing_prf_ind := Induction for typing_prf Sort Prop
                         with typing_cont_ind := Induction for typing_cont Sort Prop
                       with typing_clos_ind := Induction for typing_clos Sort Prop.
About typing_clos_ind.

Combined Scheme typing_mutind from typing_prf_ind,typing_cont_ind,typing_clos_ind.
About typing_mutind.
Lemma typing_weaken :
  (  forall A p  T (H: A|= p :+ T) E F G,
       A=E&G -> 
       ok (E & F & G) ->  (E & F & G) |= p :+ T)
/\ (forall A e T (H:(A) |= e :- T) E F G,
A=E&G ->  ok (E & F & G) ->   (E & F & G) |= e :- T)
/\ (forall A c  (H: (c:* A)) E F G,
 A=E&G -> ok (E & F & G) ->   c:* (E & F & G)) .
Proof.
  apply (typing_mutind ).
  + intros A a T OkA Binds E F G HA Ok.
    apply* typing_prf_var. apply* binds_weaken.
    rewrite HA in Binds.
    assumption.
  + intros L A U T p Ha IH E F G HA Ok.
    apply_fresh typing_abs.
    rewrite <- concat_assoc.
    apply* IH.
    rewrite HA.
    rewrite <-concat_assoc.
    reflexivity.
    rewrite concat_assoc.
    apply* ok_push.
  + intros L A T c Ha IH E F G HA Ok.
    apply_fresh (@typing_mu). 
    rewrite <- concat_assoc.
    apply* (IH y) .
    rewrite HA.
    rewrite <- concat_assoc.
    reflexivity.
    rewrite concat_assoc.
    apply* ok_push.
  + intros A a T OkA Binds E F G HA Ok.     
    apply* typing_cont_var.
    rewrite HA in Binds.
    apply* binds_weaken.
  + intros L A T c Ha IH E F G HA Ok.
    apply_fresh typing_mut.
    rewrite <- concat_assoc.
    apply* (IH y).
    rewrite concat_assoc.
    rewrite* HA.
    rewrite concat_assoc.
    apply* ok_push. 
  + intros A U T q e Hq IHq He IHe E F G HA Ok.
    apply* typing_stack.
  + intros A T p e Hp IHp He IHe E F G HA Ok.
    rewrite HA in *.
    apply (@typing_closure (E&F&G) T); [apply* IHp|apply* IHe].
Qed.    


Lemma typing_prf_weaken: forall G E F p T,
 (E & G) |= p :+ T -> ok (E & F & G) ->  (E & F & G) |= p :+ T.
Proof.
  destruct typing_weaken as [Hp _ ].
  intros;apply* Hp.
Qed.

Lemma typing_cont_weaken: forall  G E F e T,
 (E & G) |= e :- T -> ok (E & F & G) ->   (E & F & G) |= e :- T.
Proof.
  destruct typing_weaken as [_ (He,_ )].
  intros;apply* He.
Qed.

Lemma typing_clos_weaken: forall G E F c,
c:*(E & G) ->  ok (E & F & G) ->   c:* (E & F & G) .
Proof.
  destruct typing_weaken as [_ (_,Hc)].
  intros;apply* Hc.
Qed.

(** Typing is preserved by substitution. *)

  
Fixpoint typing_subst_prf F U E p T z q (H:(E & z ~ pos U & F) |= p:+ T) {struct H}:
  E |= q :+ U -> (E & F) |= [z ~+> q]+ p :+ T
with typing_subst_cont F U E e T z q (H:(E & z ~ pos U & F) |= e:- T ) {struct H}:
   E |= q :+ U -> (E & F) |= [z ~+> q]- e :- T
with typing_subst_clos F U E c z q (H:c:* (E & z ~ pos U & F)) {struct H}:
   E |= q :+ U -> [z ~+> q]* c :* (E&F).
Proof.
  - introv Typq.
    inductions H;introv; simpl.
    + case_var.
      * apply binds_middle_eq_inv in H0.
        inversion H0.
        apply_empty* typing_prf_weaken.
        assumption.
      * apply* typing_prf_var.
        apply* binds_subst.
    + apply_fresh typing_abs.
      rewrite* subst_open_prf_prf_var. 
      apply_ih_bind* H0.
    + apply_fresh typing_mu.
      rewrite <- concat_assoc.
      assert (y \notin L) by intuition.
      specialize (H y H0).
      rewrite <- concat_assoc in H.
      destruct (typing_subst_clos (F & y~negl (neg T)) U E c z q H).
      assumption.
      apply* typing_closure.
  - introv Typq.
    inductions H;introv; simpl.
    + apply* typing_cont_var.
      destruct  (binds_middle_inv H0).
      intuition.
      destruct* H1.
      intuition.
      inversion H4.
    + apply_fresh typing_mut.
      rewrite <- concat_assoc.
      assert (y \notin L) by intuition.
      specialize (H y H0).
      rewrite <- concat_assoc in H.
      destruct* (typing_subst_clos (F & y ~ pos T) U E c z q H).
      apply* typing_closure.
    + apply typing_stack.
      * apply (typing_subst_prf F U E q0 T z q H Typq).
      * apply (typing_subst_cont F U E e (neg U0) z q H0 Typq).
  - intro Typq.
    inductions H;introv;simpl.
    apply (@typing_closure (E&F) T).    
    * apply (typing_subst_prf F U E p T z q H Typq).
    * apply (typing_subst_cont F U E e (neg T) z q H0 Typq).

Admitted.

(** Preservation (typing is preserved by reduction). *)

Lemma preservation_result : preservation.
Proof.
  introv Typ. gen t'. inductions Typ; introv Red; inversions Red.
  inversions Typ1. pick_fresh x. rewrite* (@subst_intro x).
   apply_empty* typing_subst.
  apply* typing_app. 
  apply* typing_app.
Qed.

(** Progress (a well-typed term is either a value or it can 
  take a step of reduction). *)

Lemma progress_result : progress.
Proof.
  introv Typ. lets Typ': Typ. inductions Typ.
  false* binds_empty_inv. 
  left*.
  right. destruct~ IHTyp1 as [Val1 | [t1' Red1]].
    destruct~ IHTyp2 as [Val2 | [t2' Red2]].
      inversions Typ1; inversions Val1. exists* (t0 ^^ t2).
      exists* (trm_app t1 t2'). 
    exists* (trm_app t1' t2).
Qed.




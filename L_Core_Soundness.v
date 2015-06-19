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


Scheme typing_prf_ind := Induction for typing_prf Sort Prop
  with typing_cont_ind := Induction for typing_cont Sort Prop
  with typing_clos_ind := Induction for typing_clos Sort Prop.

Combined Scheme typing_mut_ind from typing_prf_ind,typing_cont_ind,typing_clos_ind.

Lemma typing_weaken :
  (  forall A p  T (H: A|= p :+ T) E F G,
       A=E&G -> 
       ok (E & F & G) ->  (E & F & G) |= p :+ T)
/\ (forall A e T (H:(A) |= e :- T) E F G,
A=E&G ->  ok (E & F & G) ->   (E & F & G) |= e :- T)
/\ (forall A c  (H: (c:* A)) E F G,
 A=E&G -> ok (E & F & G) ->   c:* (E & F & G)) .
Proof.
  apply (typing_mut_ind).
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

Lemma typing_subst_prf:
  (forall  A  p T (H: A |= p:+ T) F U E z q,
     A=(E & z ~ pos U & F) -> E |= q :+ U -> (E & F) |= [z ~+> q]+ p :+ T)
  /\(forall A e T (H: A |= e:- T ) F U E z q,
   A=(E & z ~ pos U & F)   ->   E |= q :+ U -> (E & F) |= [z ~+> q]- e :- T)
/\(forall A c (H: c:* A) F U E  z q, 
 A=(E & z ~ pos U & F) ->  E |= q :+ U -> [z ~+> q]* c :* (E&F)).
Proof.
  apply typing_mut_ind.
  - intros A a T Ok Binds F U E z q HA Typq.
    rewrite HA in *;simpl.
    + case_var.
      * apply binds_middle_eq_inv in Binds.
        inversion Binds.
        apply_empty* typing_prf_weaken.
        assumption.
      * apply* typing_prf_var.
        apply* binds_subst.
  - intros L A U T p Hp IH F T' E z q HA Typq.
    rewrite HA in *;simpl.
    apply_fresh typing_abs.
    rewrite* subst_open_prf_prf_var.
    rewrite <- concat_assoc.
    apply* IH.
    rewrite* <- concat_assoc.
  - intros L A T c Hc IH F U E z q HA Typq.
    rewrite HA in *;simpl.
    apply_fresh typing_mu.
    rewrite <- concat_assoc.
    assert (y \notin L) by intuition.
    rewrite subst_open_clos_prf_var1.
    + apply (IH y H _ U).
      * rewrite* concat_assoc.
      * assumption.
    + apply* notin_singleton.
    + destruct* (typing_regular_prf Typq).
   - intros A a T Ok Binds F U E z q HA Typq.
    rewrite HA in *;simpl.
    apply* typing_cont_var.
    destruct*  (binds_middle_inv Binds).
    destruct* H.
    intuition.
    inversion H2.
  - intros L A T c Hc IH F T' E z q HA Typq.
    rewrite HA in *;simpl.
    apply_fresh typing_mut.
    rewrite <- concat_assoc.
    assert (y \notin L) by intuition.
    rewrite subst_open_clos_prf_var.
    + apply* IH.
      rewrite* concat_assoc.
    + apply* notin_singleton.
    + destruct* (typing_regular_prf Typq).
  - intros A U T p e Hp IHp He IHe F T' E z q HA Typq.
    rewrite HA in *;simpl.
    apply typing_stack.
    + apply* IHp.
    + apply* IHe.
  - intros A T p e Hp IHp He IHe F U E z q HA Typq.
    rewrite HA in *;simpl.
    apply (@typing_closure (E&F) T).    
    * apply* IHp.
    * apply* IHe.
Qed.

(* Splitting this in three pieces *)

Lemma typing_prf_subst_prf:
  forall F U E p T z q,((E & z ~ pos U & F) |= p:+ T) ->
  E |= q :+ U -> (E & F) |= [z ~+> q]+ p :+ T.
Proof.
destruct typing_subst_prf as [Hp _ ].
intros;apply* Hp.
Qed.

Lemma typing_cont_subst_prf:
  forall F U E e T z q, (E & z ~ pos U & F) |= e:- T ->
  E |= q :+ U -> (E & F) |= [z ~+> q]- e :- T.
Proof.
  destruct typing_subst_prf as [_ (He,_)].
  intros;apply* He.
Qed.
  
Lemma typing_clos_subst_prf:
  forall F U E c z q, (c:* (E & z ~ pos U & F))->
   E |= q :+ U -> [z ~+> q]* c :* (E&F).
Proof.
  destruct typing_subst_prf as [_ (_,Hc) ].
  intros;apply* Hc.
Qed.
(* negative version *)

Lemma typing_subst_cont:
  (forall  A  p T (H: A |= p:+ T) F U E z f,
     A=(E & z ~ (neg U) & F) -> E |= f :- U -> (E & F) |= [z ~-> f]+ p :+ T)
  /\(forall A e T (H: A |= e:- T ) F U E z f,
   A=(E & z ~ (neg U) & F)   ->   E |= f :- U -> (E & F) |= [z ~-> f]- e :- T)
/\(forall A c (H: c:* A) F U E  z f, 
 A=(E & z ~ (neg U) & F) ->  E |= f :- U -> [z ~-> f]* c :* (E&F)).
Proof.
  apply typing_mut_ind.
  - intros A a T Ok Binds F U E z q HA Typq.
    rewrite HA in *;simpl.
    + apply* typing_prf_var.
      destruct* (binds_middle_inv Binds).
      destruct* H.
      destruct H as [_ (_,H)].
      inversion H.
  - intros L A U T p Hp IH F T' E z q HA Typq.
    rewrite HA in *;simpl.
    apply_fresh typing_abs.
    rewrite* subst_open_prf_cont_var1.
    rewrite <- concat_assoc.
    apply* IH.
    rewrite* <- concat_assoc.
  - intros L A T c Hc IH F U E z q HA Typq.
    rewrite HA in *;simpl.
    apply_fresh typing_mu.
    rewrite <- concat_assoc.
    assert (y \notin L) by intuition.
    rewrite subst_open_clos_cont_var.
    + apply (IH y H _ U).
      * rewrite* concat_assoc.
      * assumption.
    + apply* notin_singleton.
    + destruct* (typing_regular_cont Typq).
   - intros A a T Ok Binds F U E z q HA Typq.
    rewrite HA in *;simpl.
    case_var.
     * apply binds_middle_eq_inv in Binds.
       inversion Binds.
       apply_empty* typing_cont_weaken.
       assumption.
     * apply* typing_cont_var.
       apply* binds_subst.
  - intros L A T c Hc IH F T' E z q HA Typq.
    rewrite HA in *;simpl.
    apply_fresh typing_mut.
    rewrite <- concat_assoc.
    assert (y \notin L) by intuition.
    rewrite subst_open_clos_cont_var1.
    + apply* IH.
      rewrite* concat_assoc.
    + apply* notin_singleton.
    + destruct* (typing_regular_cont Typq).
  - intros A U T p e Hp IHp He IHe F T' E z q HA Typq.
    rewrite HA in *;simpl.
    apply typing_stack.
    + apply* IHp.
    + apply* IHe.
  - intros A T p e Hp IHp He IHe F U E z q HA Typq.
    rewrite HA in *;simpl.
    apply (@typing_closure (E&F) T).    
    * apply* IHp.
    * apply* IHe.
Qed.



(* Splitting this in three pieces *)

Lemma typing_prf_subst_cont:
  forall F U E p T z f,((E & z ~ (neg U) & F) |= p:+ T) ->
  E |= f :-  U -> (E & F) |= [z ~-> f]+ p :+ T.
Proof.
destruct typing_subst_cont as [Hp _ ].
intros;apply* Hp.
Qed.

Lemma typing_cont_subst_cont:
  forall F U E e T z f, (E & z ~  (neg U) & F) |= e:- T ->
  E |= f :-  U -> (E & F) |= [z ~-> f]- e :- T.
Proof.
  destruct typing_subst_cont as [_ (He,_)].
  intros;apply* He.
Qed.
  
Lemma typing_clos_subst_cont:
  forall F U E c z f, (c:* (E & z ~  (neg U) & F))->
   E |= f :-  U -> [z ~-> f]* c :* (E&F).
Proof.
  destruct typing_subst_cont as [_ (_,Hc) ].
  intros;apply* Hc.
Qed.




(** Preservation (typing is preserved by reduction). *)

Lemma open_clos_comm: forall p e y,  cl p e *^+ y = cl (p+^+y) (e-^+y).
Proof.
  intros.
  reflexivity.
Qed.

Lemma open_cont_proof_def : forall e y, e-^+y = {0 ~+> (prf_fvar y)}-e.  
Proof.
  intros;reflexivity.
Qed.

Lemma subject_reduction : preservation.
Proof.
  introv Typ. gen c'.
  inductions Typ;intros c Red;inversions Red.
  - inversions H0.
    inversion H3.
    pick_fresh x.
    rewrite* (@subst_intro_clos_prf x).
    apply_empty* typing_clos_subst_prf.
  - inversion H0.
    apply* (@typing_closure E T0).
    rewrite <-  H8 in *.
    inversion H.
    apply_fresh typing_mut.
    simpl.
    assert (y\notin L) by intuition.
    rewrite open_clos_comm.
    apply (@typing_closure (E&y~pos T0) U).
    + apply* H13.
    + destruct (typing_regular_cont H9).
      rewrite open_cont_proof_def.
      rewrite* <-(open_rec_cont_prf_id).
      apply_empty* typing_cont_weaken.
  - inversion H.
    pick_fresh x.
    rewrite* (@subst_intro_clos_cont x).
    apply_empty* typing_clos_subst_cont.  
Qed.

(** Progress (a well-typed term is either a value or it can 
  take a step of reduction). *)

Print progress.
About typing_mut_ind.
Search "fresh".

Lemma progress_one_step :
  (forall E (p : prf) (T : typ),
     E |= p :+ T -> E=empty ->
     value p \/(exists L,forall a, a\notin L -> exists c, red (cl p (co_fvar a)) (c)))
(*/\ (forall E (e:cont) (T : typ),
      E |= e :- T -> E=empty -> True)
/\ (forall E (c : clos) ,c :* E ->
   (E=empty -> True))*)
.
Proof.
  intros E p T Hp.
  induction Hp.
  -intros HE.
   rewrite HE in *.
   false* binds_empty_inv.
  - intros HE.
  left*.
  apply value_abs.
  apply (@proof_abs L).
  intros.
  specialize (H a H1).
  destruct* (typing_regular_prf H).
- intros HE.
  right.
  exists L.
  intros a Ha.
  exists (c*^-a).
  apply* red_mu.
  apply_fresh proof_mu.
  assert (y\notin L) as Hy by intuition.
  specialize (H y Hy).
  apply (typing_regular_clos) in H.
  destruct* H.
Qed.







  
Lemma progress_result :
  (forall E (p : prf) (T : typ),
     E |= p :+ T -> E=empty ->
     value p \/(exists L,forall a, a\notin L -> exists p' n, redn n (cl p (co_fvar a)) (cl p' (co_fvar a))))
/\ (forall E (e:cont) (T : typ),
      E |= e :- T -> E=empty -> True)
/\ (forall E (c : clos) ,c :* E ->
  forall a T, E=a~neg T ->exists p' n,  (redn n c (cl p' (co_fvar a))\/ c = cl p' (co_fvar a)) /\ E |= p' :+ T)
.
Proof.
  apply typing_mut_ind.
- intros E p T Ok Binds HE.
  rewrite HE in *.
  false* binds_empty_inv.
- intros L E U T p Hp IH  HE.
  rewrite HE in *.
  left*.
  apply value_abs.
  apply (@proof_abs L).
  intros.
  specialize (Hp a H).
  destruct* (typing_regular_prf Hp).
- intros L E T c Hc IH HE.
  rewrite HE in *.
  right.
  exists L.
  intros a Ha.
  destruct* (IH a Ha a T (concat_empty_l (a~neg T))) as (p',(n,([Red|Eq],Typ))).
  + exists p' (n+1).
    apply redS.
    exists (c *^-a).
    split.
    * apply* red_mu.
      apply_fresh proof_mu.
      assert (y\notin L) as Hy by intuition.
      specialize (Hc y Hy).
      apply (typing_regular_clos) in Hc.
      destruct* Hc as (_,Ok).
    * assumption.
  + exists p' 1.
    apply red1.        
    rewrite <- Eq.
    apply* red_mu.
    apply_fresh proof_mu.
    assert (y\notin L) as Hy by intuition.
    specialize (Hc y Hy).
    apply (typing_regular_clos) in Hc.
    destruct* Hc as (_,Ok).
- tauto.
- tauto.
- tauto.
- intros E T p e Hp IHp He _ a U HE.
  rewrite HE in *.
  inversion He.
  + apply binds_single_inv in H0.
    destruct H0.
    inversion H4.
    subst.
    exists p 0.
    split~.
    + admit.
  + subst.
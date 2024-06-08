Require Import NArith.
Require Import List.
Import ListNotations.
Open Scope type.

Parameter (f : N -> N).
Parameter (g : N -> N).

Inductive ext_event :=
    | Enq (x : N)
    | Deq.

Definition impl_t := list N * list N * list N.
Definition spec_t := list N.

(* Observation for impl system *)
Definition first_impl (state : impl_t) (ret : N) : Prop :=
    exists i m o e, state = (i, m, o++[e]) /\ ret = e.

(* Observation for spec system *)
Definition first_spec (state : spec_t) (ret : N) : Prop :=
    exists o e, state = (o++[e]) /\ ret = e.

Definition masquerade (i: impl_t) (s: spec_t) : Prop :=
    forall ret, first_impl i ret -> first_spec s ret.

Inductive rules_impl_sig :=
    | doF | doG.

Inductive rule_impl :  impl_t -> impl_t -> rules_impl_sig -> Prop := 
    | case1 : forall a b c d,
         rule_impl (a ++ [b], c, d) (a, [f(b)] ++ c, d) doF
    | case2 : forall a b c d,
         rule_impl (a, b ++ [c], d) (a, b, [g(c)] ++ d) doG.

Inductive rules_impl :  impl_t -> impl_t -> Prop := 
    | none : forall a b c,
        rules_impl (a, b, c) (a, b, c)
    | one_more : forall a b c d e f g h i r,
        rules_impl (a,b,c) (d,e,f) ->
        rule_impl (d,e,f) (g,h,i) r -> 
        rules_impl (a,b,c) (g,h,i).

Inductive am_step_impl : impl_t -> impl_t -> ext_event -> Prop :=
    | impl_enq : forall i e m o, am_step_impl (i, m, o) ([e] ++ i,  m, o) (Enq e)
    | impl_deq : forall i e m o, am_step_impl (i, m, o ++ [e]) (i,  m, o) Deq.

Inductive am_step_spec : spec_t -> spec_t -> ext_event -> Prop :=
    | spec_enq : forall i e, am_step_spec (i) ([g(f(e))] ++ i) (Enq e)
    | spec_deq : forall i e, am_step_spec (i ++ [e]) (i) Deq.

Definition ϕ (i : impl_t) (s: spec_t): Prop :=
    match i, s with 
    | (imp_i, imp_mid, imp_out), (spec_in) => 
        map (fun x => g(f(x))) imp_i ++
        map g imp_mid ++ 
        imp_out 
        = spec_in
    end.

Ltac cleanup := intros;
  repeat (subst;match goal with
  | H: _ /\ _ |- _ => destruct H
  | H: exists _, _  |- _ => destruct H
  | H: ?a = ?a |- _ => clear H
  end).

Theorem ϕ_forward_internal : forall i s, 
    ϕ i s -> 
    forall r i' ,
    (rule_impl i i' r) ->
    ϕ i' s.
    intros.
    unfold ϕ in *.
    destruct r.
    {
        inversion H0; subst.
        simpl in *.
        clear H0.
        rewrite map_app in H.
        rewrite <- H.
        simpl.
        rewrite <- app_assoc.
        simpl.
        trivial.
    }
    {
        inversion H0; subst.
        simpl in *.
        clear H0.
        rewrite map_app in H.
        rewrite <- H.
        simpl.
        rewrite <- app_assoc.
        simpl.
        trivial.
    }
    Qed.


Theorem ϕ_forward_methods : forall i s, 
    ϕ i s -> 
    forall e i' ,
    (am_step_impl i i' e) ->
    exists s_inter, 
    am_step_spec s s_inter e /\ 
    ϕ i' s_inter.
    intros i s ϕ e.
    case e.
    {
        intros x i' H.
        inversion H.
        subst.
        clear H.
        eexists.
        simpl in ϕ |- *.
        rewrite <- ϕ.
        split.
        econstructor.
        rewrite ϕ.
        simpl.
        trivial.
    }
    {
        intros i' H.
        inversion H.
        subst.
        clear H.
        simpl in ϕ |- *.
        rewrite <- ϕ.
        rewrite app_assoc.
        rewrite app_assoc.
        eexists.
        split.
        econstructor.
        rewrite <- app_assoc.
        trivial.
    }
    Qed.
    
Theorem  ϕ_implies_indist : forall i s, 
    ϕ i s -> masquerade i s.
    intros i s H.
    cbv [ϕ masquerade first_impl first_spec] in *.
    intros ret P.
    cleanup.
    subst.
    rewrite <- H.
    eexists.
    eexists.
    split; eauto.
    rewrite app_assoc.
    rewrite app_assoc.
    trivial.
Qed.

(* Now with an inductive phi: *)

Inductive ϕ' : impl_t -> spec_t -> Prop :=
    | flush : forall l, ϕ' ([], [], l) (l)
    | bw_f: forall i i' s,
        rule_impl i i' doF ->
        ϕ' i' s ->
        ϕ' i s
    | bw_g: forall i i' s,
        rule_impl i i' doG ->
        ϕ' i' s ->
        ϕ' i s.


Theorem ϕ'_forward_internal : forall i s, 
    ϕ' i s -> 
    forall r i' ,
    (rule_impl i i' r) ->
    ϕ' i' s.
    induction 1.
    -
        firstorder.
        inversion H.
        subst.
        destruct a; inversion H1; eauto.
        (* inversion H. *)
        subst.
        destruct b; inversion H2; eauto.
    -
        cleanup.
        destruct r.
        * 
          inversion H.
          inversion H1.
          subst.
          inversion H.
          cleanup.
          subst.
          inversion H4.
          eapply app_inj_tail_iff in H3.
          eapply app_inj_tail_iff in H5.
          cleanup.
          eauto.
        * intros.
          inversion H; cleanup.
          inversion H1; cleanup.
          subst.
          inversion H4.
          subst.
          clear H4.
          clear H H1.
          eapply bw_f.
          econstructor.
          eapply IHϕ'.
          rewrite app_assoc.
          econstructor.
     - (* Same case symmetry *)
        cleanup.
        destruct r.
        * intros.
          inversion H; cleanup.
          inversion H1; cleanup.
          subst.
          inversion H4.
          subst.
          clear H4.
          clear H H1.
          eapply bw_g.
          rewrite app_assoc.
          econstructor.
          eapply IHϕ'.
          econstructor.
        * 
          inversion H.
          inversion H1.
          subst.
          inversion H.
          cleanup.
          subst.
          inversion H4.
          eapply app_inj_tail_iff in H5.
          eapply app_inj_tail_iff in H6.
          cleanup.
          eauto.
    Qed.
       
Theorem ϕ'_forward_methods : forall i s, 
    ϕ' i s -> 
    forall e i' ,
    (am_step_impl i i' e) ->
    exists s_inter, 
    am_step_spec s s_inter e /\ 
    ϕ' i' s_inter.
    induction 1.
    -
        firstorder.
        inversion H.
        {
            subst.
            eexists.
            split.
            econstructor.
            eapply bw_f.
            simpl.
            replace ([e0]) with ([]++ [e0]).
            eapply case1.
            eauto.
            eapply bw_g.
            simpl.
            replace ([f e0]) with ([]++ [f e0]).
            eapply case2.
            eauto.
            eapply flush.
        }
        {
            subst.
            inversion H.
            subst.
            eapply app_inj_tail_iff in H3.
            cleanup. 
            eexists.
            split.
            econstructor.
            econstructor.
        }
    -
        (* method/rule commutation *)
        firstorder.
        cleanup.
        destruct e.
        * intros.
          inversion H; cleanup.
          inversion H1; cleanup.
          subst.
          inversion H4.
          subst.
          clear H4.
          specialize (IHϕ' (Enq x)).
          assert (exists i' , am_step_impl (a, [f b] ++ c, d) i' (Enq x)).
          eexists.
          econstructor.
          cleanup.
          inversion H2.
          subst.
          specialize (IHϕ') with (1:= H2).
          cleanup.
          inversion H3.
          subst.
          eexists.
          split.
          econstructor.
          eapply bw_f; eauto.
          rewrite app_assoc.
          econstructor.
        * 
          inversion H; cleanup.
          inversion H1; cleanup.
          subst.
          inversion H4.
          subst.
          clear H4.
          specialize (IHϕ' Deq).
          assert (exists i' , am_step_impl (a, [f b] ++ c, o ++ [e]) i' Deq).
          eexists.
          econstructor.
          cleanup.
          inversion H2.
          subst.
          eapply app_inj_tail_iff in H6.
          cleanup; eauto.
          subst.
          specialize (IHϕ') with (1:= H2).
          cleanup.
          inversion H3.
          subst.
          eexists.
          split.
          econstructor.
          eapply bw_f; eauto.
          econstructor.
    -
        (* method/rule commutation *)
        firstorder.
        cleanup.
        destruct e.
        * intros.
          inversion H; cleanup.
          inversion H1; cleanup.
          subst.
          inversion H4.
          subst.
          clear H4.
          specialize (IHϕ' (Enq x)).
          assert (exists i' , am_step_impl (a, b, [g c] ++ d) i' (Enq x)).
          eexists.
          econstructor.
          cleanup.
          inversion H2.
          subst.
          specialize (IHϕ') with (1:= H2).
          cleanup.
          inversion H3.
          subst.
          eexists.
          split.
          econstructor.
          eapply bw_g; eauto.
          econstructor.
        * 
          inversion H; cleanup.
          inversion H1; cleanup.
          subst.
          inversion H4.
          subst.
          clear H4.
          specialize (IHϕ' Deq).
          assert (exists i' , am_step_impl (a, b, [g c] ++ o ++ [e]) i' Deq).
          eexists.
          rewrite app_assoc.
          econstructor.
          cleanup.
          inversion H2.
          subst.
          Search (?a::?b ++ ?c).
          rewrite app_comm_cons in H6.
          eapply app_inj_tail_iff in H6.
          cleanup; eauto.
          subst.
          specialize (IHϕ') with (1:= H2).
          cleanup.
          inversion H3.
          subst.
          eexists.
          split.
          econstructor.
          eapply bw_g; eauto.
          econstructor.
    Qed.

Theorem  ϕ'_implies_indist : forall i s, 
    ϕ' i s -> masquerade i s.
    induction 1.
    -   cbv [masquerade].
        intros.
        cbv [first_spec first_impl] in *.
        cleanup.
        inversion H.
        subst.
        eexists.
        eexists.
        split; eauto.
    -   cbv [masquerade] in *.
        intros.
        cbv [first_spec first_impl] in *.
        cleanup.
        subst.
        inversion H.
        subst.
        clear H.
        specialize (IHϕ' x2).
        match type of IHϕ' with 
        | ?a -> ?b => assert a 
        end. 
        eexists; eauto.
        specialize (IHϕ' H).
        cleanup.
        subst.
        eexists; eauto.
    -   cbv [masquerade] in *.
        intros.
        cbv [first_spec first_impl] in *.
        cleanup.
        subst.
        inversion H.
        subst.
        clear H.
        specialize (IHϕ' x2).
        match type of IHϕ' with 
        | ?a -> ?b => assert a 
        end. 
        eexists; eexists; eexists; eexists; eauto.
        split; eauto.
        rewrite app_assoc.
        eauto.
        specialize (IHϕ' H).
        cleanup.
        subst.
        eexists; eauto.
Qed.


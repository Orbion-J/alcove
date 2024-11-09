Require Import Sets.Ensembles.
Require Import Sets.Powerset.
Require Import String.
Require Import List.
Require Import Lists.ListSet.
Require Import Logic.FunctionalExtensionality.

Module Automaton.

	Variant INTERNAL_STATE (s:Set) (o:Set) (c:Set) (f:Set) :=
		| Structural : s -> INTERNAL_STATE s o c f 
		| Observation : o -> INTERNAL_STATE s o c f
		| Choice : c -> INTERNAL_STATE s o c f 
		| Final : f -> INTERNAL_STATE s o c f 
	.

	Record AUTOMATON := {
		structural_states : Set ;
		observation_states : Set ;
		choice_states : Set ;
		final_states : Set ;
		states := INTERNAL_STATE structural_states observation_states choice_states final_states ;
		initial : structural_states ;
		modifiers : Set ;
		observable : Set ;
		choices : Set ;
		structural_transition : structural_states -> (modifiers * states) ;
		observation_transition : observation_states -> (observable * states * states) ;
		choice_transition : choice_states -> Ensemble (choices * states) ;
	}.

End Automaton.

Module Type TYP_PARAM_SIG.
	Parameter primitive_types : Set.
	Parameter eq_dec_primitive_types :
		forall x y:primitive_types, {x = y} + {x <> y}.
End TYP_PARAM_SIG.

Module TYP (X : TYP_PARAM_SIG).
	Inductive Typ := 
		| Fun : Typ -> Typ -> Typ
		| ActT | ModT | ChoT | ReqT
		| PTyp : X.primitive_types -> Typ
	.

	Inductive function_type (domain:Typ) : Typ -> Prop :=
		| function_type_0 : function_type domain domain
		| function_type_fun : forall t t', function_type domain t -> function_type domain (Fun t' t)
	.

	Definition primitive_modifiersT : Ensemble Typ := function_type ModT.
	Definition primitive_actorsT : Ensemble Typ := function_type ActT.
	Definition primitive_choicesT : Ensemble Typ := function_type ChoT.
	Definition valuesT : Ensemble Typ := fun t =>
		exists pt: X.primitive_types, function_type (PTyp pt) t.
	
End TYP.



Module Type LANGUAGE_PARAM_SIG (TYP_PARAM : TYP_PARAM_SIG) .
	Export TYP_PARAM.

	Parameter values : Set.
	Parameter primitive_modifiers : Set.
	Parameter primitive_actors : Set.
	Parameter primitive_choices : Set.

	Module TYP := TYP TYP_PARAM.

	Parameter type_values : values -> TYP.Typ.
	Parameter type_values_valuesT : forall v, TYP.valuesT (type_values v).
	Parameter type_modifiers : primitive_modifiers -> TYP.Typ.
	Parameter type_modifiers_primitive_modifersT : forall v, TYP.primitive_modifiersT (type_modifiers v).
	Parameter type_actors : primitive_actors -> TYP.Typ.
	Parameter type_actors_primitive_modifersT : forall v, TYP.primitive_actorsT (type_actors v).
	Parameter type_choices : primitive_choices -> TYP.Typ.
	Parameter type_choices_primitive_modifersT : forall v, TYP.primitive_choicesT (type_choices v).

End LANGUAGE_PARAM_SIG.

Module LANGUAGE (TYP_PARAM:TYP_PARAM_SIG) (LANGUAGE_PARAM : LANGUAGE_PARAM_SIG TYP_PARAM).
	Import LANGUAGE_PARAM.
	Import TYP.

	Definition ident := string.

	Inductive L :=
		| Var : ident -> L
		| App : L -> L -> L
		| Abs : ident -> Typ -> L -> L
		| Seq : L -> L -> L
		| Req : L -> L -> L
		| Val : values -> L 
		| PMod : primitive_modifiers -> L 
		| PAct : primitive_actors -> L 
		| PCho : primitive_choices -> L
	.

	Definition ctx := ident -> option Typ.
	Definition ctx_in x t (G:ctx) := G x = Some t.
	Definition ctx_notin x (G:ctx) := G x = None.
	Definition ctx_empty : ctx := fun _ => None.
	Definition ctx_add x t (G:ctx) : ctx := fun y => match string_dec x y with
		| left _ => Some t
		| right _ => G y
	end.
	Definition ctx_one x t : ctx := ctx_add x t ctx_empty.
	Definition ctx_added x t G H :=
		ctx_notin x G /\ H = ctx_add x t G.
	Definition ctx_joined (G G' H:ctx) :=
		forall x t, ctx_in x t H <-> (ctx_in x t G \/ ctx_in x t G').

	Lemma ctx_one_in : forall x t, ctx_in x t (ctx_one x t).
	Proof.
		intros.
		unfold ctx_in. unfold ctx_one. unfold ctx_add. destruct string_dec; auto. contradiction.
	Qed.
	Lemma ctx_in_fun : forall G x t t', ctx_in x t G -> ctx_in x t' G -> t = t'.
	Proof.
		intros. unfold ctx_in in *. 
		assert (Some t = Some t'). rewrite <- H. auto.
		inversion H1. auto.
	Qed.
	Lemma ctx_joined_unique : forall G G' H x t t',
		ctx_joined G G' H -> ctx_in x t G -> ctx_in x t' G' -> t = t'.
	Proof.
		intros.
		assert (ctx_in x t H) by (apply H0; auto).
		assert (ctx_in x t' H) by (apply H0; auto).
		eapply ctx_in_fun; eauto. 
	Qed.
	Lemma ctx_add_inj : forall G H x t, 
		ctx_notin x G -> ctx_notin x H -> ctx_add x t G = ctx_add x t H -> G = H.
	Proof.
		intros. extensionality y. 
		destruct (string_dec x y).
		- unfold ctx_notin in *. subst. rewrite H1, H0. auto.
		- assert (G y = (ctx_add x t G) y). unfold ctx_add. destruct (string_dec x y); auto. contradiction. 
			assert (H y = (ctx_add x t H) y). unfold ctx_add. destruct (string_dec x y); auto. contradiction. 
			rewrite H3, H4, H2. auto.
	Qed.
	Lemma ctx_joined_fun : forall G G' H H0, ctx_joined G G' H -> ctx_joined G G' H0 -> H = H0.
	Proof.
		intros. 
		assert (forall x t, ctx_in x t H <-> ctx_in x t H0).
		- intros. split; intro; assert (ctx_in x t G \/ ctx_in x t G').
			apply H1; auto. apply H2; auto. 
			apply H2; auto. apply H1; auto.
		- extensionality x.
			set (v := H x). assert (H x = v) by auto. 
			set (w := H0 x). assert (H0 x = w) by auto. 
			destruct v; destruct w; auto.
			+ enough (t=t0) by (subst; auto). eapply ctx_in_fun. apply H4. apply H3. auto.
			+ apply H3 in H4. unfold ctx_in in H4. rewrite <- H4. auto.
			+ apply H3 in H5. unfold ctx_in in H5. rewrite <- H4. auto.
	Qed.



	Reserved Notation "G |- l ! t" (at level 80).

	Inductive typ : ctx -> L -> Typ -> Prop :=
		| typ_var : forall x t, ctx_one x t |- Var x ! t
		| typ_app : forall a b t u G G' H, ctx_joined G G' H ->
			G |- a ! Fun t u -> G' |- b ! t -> H |- App a b ! u
		| typ_abs : forall G x t a, ctx_notin x G ->
			ctx_add x t G |- a ! ModT -> G |- Abs x t a ! ModT
		| typ_seq : forall G G' H a b, ctx_joined G G' H ->
			G |- a ! ModT -> G' |- b ! ModT -> H |- Seq a b ! ModT
		| typ_req : forall G G' H a b, ctx_joined G G' H ->
			G |- a ! ActT -> G' |- b ! ChoT -> H |- Req a b ! ReqT 
		| typ_val : forall v,
			ctx_empty |- Val v ! type_values v
		| typ_mod : forall m,
			ctx_empty |- PMod m ! type_modifiers m
		| typ_act : forall a,
			ctx_empty |- PAct a ! type_actors a
		| typ_cho : forall c,
			ctx_empty |- PCho c ! type_choices c
	where "G |- a ! t" := (typ G a t).

	(* Lemma ctx_unicity : forall G a t, G |- a ! t -> forall H b u, H |- b ! u -> 
		a = b -> t=u -> G = H.
	Proof.
		intros ? ? ? H0; induction H0; intros ? ? ? H1; induction H1;
		intros Hterm; inversion Hterm; intro Htyp; inversion Htyp; subst; auto. 
		- assert (G = G0). 
		
		
		eapply IHtyp1; eauto. 
			assert (G' = G'0). eapply IHtyp2; eauto. 
			subst. eapply ctx_joined_fun; eauto.	
		- assert (ctx_add x0 t0 G = ctx_add x0 t0 G0).
			eapply IHtyp; eauto. eapply ctx_add_inj; eauto.
		- assert (G = G0). eapply IHtyp1; eauto. 
			assert (G' = G'0). eapply IHtyp2; eauto. 
			subst. eapply ctx_joined_fun; eauto.	
		- assert (G = G0). eapply IHtyp1; eauto. 
			assert (G' = G'0). eapply IHtyp2; eauto. 
			subst. eapply ctx_joined_fun; eauto.
	Qed. *)


	(* Lemma typ_ctx_unicity : forall G a t, G |- a ! t -> forall H b u, H |- b ! u -> 
		a = b -> (G = H <-> t=u).
	Proof.
		intros ? ? ? H0; induction H0; intros ? ? ? H1; induction H1;
		intros Hterm; inversion Hterm; split; intro; subst; auto.
		- eapply ctx_in_fun. eapply ctx_one_in. rewrite H. apply ctx_one_in.
		- enough (Fun t u = Fun t u0).
			+ inversion H; auto.
			+ assert (t=t0).
				* eapply IHtyp2; eauto. admit.
			  	* admit.
		- assert (G = G0). {
			eapply IHtyp1; eauto. enough (t=t0) by (subst; auto).
			eapply IHtyp2; eauto.
			assert (G' = G'0). eapply IHtyp2; eauto. 
			subst. eapply ctx_joined_fun; eauto.
		- assert (ctx_add x0 t0 G = ctx_add x0 t0 G0).
			eapply IHtyp; eauto. eapply ctx_add_inj; eauto.
		- assert (G = G0). eapply IHtyp1; eauto. 
			assert (G' = G'0). eapply IHtyp2; eauto. 
			subst. eapply ctx_joined_fun; eauto.
		- assert (G = G0). eapply IHtyp1; eauto. 
			assert (G' = G'0). eapply IHtyp2; eauto. 
			subst. eapply ctx_joined_fun; eauto.
	Qed. *)
(* 
	Definition ctx := set (ident * Typ).
	Lemma Typ_eq_dec : forall x y:Typ, {x = y} + {x <> y}.
	Proof.
		induction x; induction y.
		all:try (right; intro HH; inversion HH; fail).
		all:try (left; auto; fail).
		- destruct (IHx1 y1).
			destruct (IHx2 y2); subst; auto.
			all:right; intro HH; inversion HH; auto.
		- destruct (eq_dec_primitive_types p p0). left; subst; auto. right; intro; inversion H; auto.
	Qed.
	Lemma ident_eq_dec : forall x y:ident, {x = y} + {x <> y}.
	Proof. apply string_dec. Qed.
	Lemma ctx_eq_dec : forall x y:(ident * Typ), {x = y} + {x <> y}.
	Proof.
		intros. destruct x; destruct y.
		destruct (Typ_eq_dec t t0); subst.
		- destruct (ident_eq_dec i i0); subst.
			+ auto.
			+ right. intro. inversion H. auto.
		- right. intro. inversion H. auto.
	Qed.
	Definition set_union := set_union ctx_eq_dec.
	Definition set_add := set_add ctx_eq_dec.
	Definition set_mem := set_mem ctx_eq_dec.
	Definition set_remove := set_remove ctx_eq_dec.


	Reserved Notation "G |- l ! t" (at level 80).

	Inductive typ : ctx -> L -> Typ -> Prop :=
		| typ_var : forall x t, (x,t)::nil |- Var x ! t
		| typ_app : forall a b t u G H,
			G |- a ! Fun t u -> H |- b ! t -> (set_union G H) |- App a b ! u
		| typ_abs : forall G x t a, set_In (x,t) G -> 
			G |- a ! ModT -> set_remove (x,t) G |- Abs x t a ! ModT
		| typ_seq : forall G H a b, 
			G |- a ! ModT -> H |- b ! ModT -> set_union G H |- Seq a b ! ModT
		| typ_req : forall G H a b,
			G |- a ! ActT -> H |- b ! ChoT -> set_union G H |- Req a b ! ReqT 
		| typ_val : forall v,
			nil |- Val v ! type_values v
		| typ_mod : forall m,
			nil |- PMod m ! type_modifiers m
		| typ_act : forall a,
			nil |- PAct a ! type_actors a
		| typ_cho : forall c,
			nil |- PCho c ! type_choices c
	where "G |- a ! t" := (typ G a t).

	Lemma typ_unicity : forall G a t u, G |- a ! t -> G |- a ! u -> t=u.
	Proof.
		enough (forall G a t, G |- a ! t -> forall H b u, H |- b ! u -> a = b -> G = H -> t=u) by eauto. 
		intros ? ? ? H0; induction H0; intros ? ? ? H1; induction H1; intros Hterm Hctx.
		all: inversion Hterm; inversion Hctx; subst; auto.
		assert (t = t0).
		{ eapply IHtyp2; eauto. }
		assert (Fun t u = Fun t u0). 
		- eapply IHtyp1. eauto.
		- inversion H1.
		eauto.

	Lemma ctx_unicity : forall G H a t, G |- a ! t -> H |- a ! t -> G = H.
	Proof.
		enough (forall G a t, G |- a ! t -> forall H b u, H |- b ! u -> a = b -> t = u -> G = H) by eauto. 
		intros ? ? ? H0; induction H0; intros ? ? ? H1; induction H1; intros Hterm Htyp.
		all: inversion Hterm; inversion Htyp; subst; auto.
		eauto.
		 *)

End LANGUAGE.
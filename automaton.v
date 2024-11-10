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
	Definition ctx_in' x (G:ctx) := exists t, G x = Some t.
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
	Lemma ctx_joined_in' : forall G G' H x, ctx_joined G G' H ->
		(ctx_in' x G \/ ctx_in' x G' <-> ctx_in' x H).
	Proof.
		intros; split; intros.
		- destruct H1 as [ [t] | [t] ]; exists t; apply H0; auto.
		- destruct H1 as [t]. edestruct H0 as [[]_]. eauto. 
			+ left. exists t. auto.  
			+ right. exists t. auto.  
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

	Fixpoint appears x a := match a with 
		| Var y => x = y
		| App a b => appears x a \/ appears x b
		| Abs y _ a => not (x = y) /\ appears x a
		| Seq a b => appears x a \/ appears x b
		| Req a b => appears x a \/ appears x b
		| _ => False
	end.

	Lemma ctx_minimal : forall a G t, G |- a ! t -> forall x, appears x a -> ctx_in' x G.
	Proof.
		intros ? ? ? Ht. induction Ht; intros xx HH; inversion HH; subst; auto.
		all: try (eapply ctx_joined_in'; eauto; fail).
		- exists t. apply ctx_one_in.
		- destruct (IHHt xx H1) as [t']. 
			unfold ctx_add in H2. destruct (string_dec x xx).
			+ exfalso. apply H0. auto.
			+ exists t'. auto.
	Qed. 
	Lemma ctx_minimal' : forall G a t, G |- a ! t -> forall x, ctx_in' x G -> appears x a.
	Proof.
		intros ? ? ? Ht. induction Ht; intros xx HH; inversion HH; subst; auto.
		-  unfold appears.
			unfold ctx_one in H. unfold ctx_add in H. destruct (string_dec x xx); auto.
			unfold ctx_empty in H. inversion H.
		- unfold appears. destruct HH as [ t']. destruct (H0 xx t') as [[] _]. eauto. 
			+ left. apply IHHt1. exists t'. auto.
			+ right. apply IHHt2. exists t'. auto.
		- unfold appears. 
			assert (x <> xx).
			{ intro. subst. unfold ctx_notin in H. rewrite H in H0. inversion H0. }
			split ; auto. apply IHHt.
			exists x0. unfold ctx_add. destruct (string_dec x xx).
			+ exfalso. apply H1. auto.
			+ auto. 
		- unfold appears. destruct HH as [ t']. destruct (H0 xx t') as [[] _]. eauto. 
			+ left. apply IHHt1. exists t'. auto.
			+ right. apply IHHt2. exists t'. auto. 
		- unfold appears. destruct HH as [ t']. destruct (H0 xx t') as [[] _]. eauto. 
			+ left. apply IHHt1. exists t'. auto.
			+ right. apply IHHt2. exists t'. auto.
		- unfold ctx_empty in H. inversion H.
		- unfold ctx_empty in H. inversion H.
		- unfold ctx_empty in H. inversion H.
		- unfold ctx_empty in H. inversion H.
	Qed.	

	Lemma ctx_joined_in'_inj_left : forall G G' G0 G'0 H, ctx_joined G G' H -> ctx_joined G0 G'0 H -> 
		(forall x, ctx_in' x G <-> ctx_in' x G0) -> G = G0.
	Proof.
		intros. extensionality x.
		set (v := G x). assert (G x = v) by auto.
		set (w := G0 x). assert (G0 x = w) by auto.
		destruct v; destruct w; auto.
		- assert (ctx_in x t H). apply H0. left. apply H3.
			assert (ctx_in x t0 H). apply H1. left. apply H4.
			rewrite <- H5. auto.
		- destruct (H2 x) as [? _]. destruct H5. exists t; auto.
			rewrite H4 in H5; inversion H5.
		- destruct (H2 x) as [_ ?]. destruct H5. exists t; auto.
			rewrite H3 in H5; inversion H5.
	Qed.

	Lemma ctx_joined_in'_inj_right : forall G G' G0 G'0 H, ctx_joined G G' H -> ctx_joined G0 G'0 H -> 
		(forall x, ctx_in' x G' <-> ctx_in' x G'0) -> G' = G'0.
	Proof.
		intros. extensionality x.
		set (v := G' x). assert (G' x = v) by auto.
		set (w := G'0 x). assert (G'0 x = w) by auto.
		destruct v; destruct w; auto.
		- assert (ctx_in x t H). apply H0. right. apply H3.
			assert (ctx_in x t0 H). apply H1. right. apply H4.
			rewrite <- H5. auto.
		- destruct (H2 x) as [? _]. destruct H5. exists t; auto.
			rewrite H4 in H5; inversion H5.
		- destruct (H2 x) as [_ ?]. destruct H5. exists t; auto.
			rewrite H3 in H5; inversion H5.
	Qed.
			

	Lemma typ_unicity : forall G a t u, G |- a ! t -> G |- a ! u -> t = u.
	Proof.
		enough (forall G a t, G |- a ! t -> forall H b u, H |- b ! u -> a = b -> G = H -> t = u)
		by eauto.
		intros ? ? ? H0; induction H0; intros ? ? ? H1; induction H1;
		intros Hterm; inversion Hterm; intro; subst; auto.
		- eapply ctx_in_fun. eapply ctx_one_in. rewrite H. apply ctx_one_in.
		- enough (Fun t u = Fun t u0).
			+ inversion H; auto.
			+ assert (t=t0).
				* eapply IHtyp2; eauto. eapply ctx_joined_in'_inj_right; eauto.
					intro. split; intro; eapply ctx_minimal; eauto; eapply ctx_minimal'.
					-- apply H0_0.
					-- auto.
					-- apply H1_0.
					-- auto.
			  	* subst. eapply IHtyp1; eauto. eapply ctx_joined_in'_inj_left; eauto.
					intro. split; intro; eapply ctx_minimal; eauto; eapply ctx_minimal'.
					-- apply H0_.
					-- auto.
					-- apply H1_.
					-- auto.
	Qed.

End LANGUAGE.
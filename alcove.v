Require Import List.
Require Import String.

(*
	** Notations **

	- [A] => [B]          MEANS that the rule number [A] is implemented at rule number [B]
	- => [A]              MEANS that the current rule is implemented at rule number [A]
	- <= [A]              MEANS that the rule number [A] is implemented at that point
	- [A] =>              MEANS that the rule number [A] is implemented later
	- ntd                 MEANS "nothing to do" : the rule does not need anything to be implemented
	- physical descrption MEANS that the rule descirbes the physical game pieces, there is nothing to implement

*)

Section __CARDS.

	Axiom CARD : Type.

End __CARDS.

Section __PLAYERS.

	Axiom PLAYER : Type.
	(* Variant PLAYER := PlayerA | PlayerB . *)

End __PLAYERS.

Section _2_OBJECTS.

	Axiom OBJECT : Type.

	(*****************************)
	(*** 2.2 - CHARACTERISTICS ***)
	(*****************************)

	Axiom has : OBJECT -> forall Characteristic:Type, Characteristic -> Prop.

	Fixpoint has_at_least (x:OBJECT) (Characteristic:Type) (cs:list Characteristic) :=
		match cs with
			  nil => True 
			| cons c cs => has x Characteristic c /\ has_at_least x Characteristic cs 
		end.
	Definition has_among (x:OBJECT) (Characteristic:Type) (cs:list Characteristic) :=
		forall c:Characteristic, has x Characteristic c -> In c cs.
	Definition has_exactly (x:OBJECT) (Characteristic:Type) (cs:list Characteristic) :=
		has_at_least x Characteristic cs  /\ has_among x Characteristic cs.

	Axiom is_TOKEN : OBJECT -> Prop.

	(*------------------*)
	(*   2.2.1 - TYPE   *)
	(*------------------*)

	(* 2.2.1.a *)
	Variant TYPE :=
		| Character
		| Emblem
		| Hero
		| ManaOrb
		| Permanent 
		| Region
		| Spell
	.

	(* 2.2.1.b *)
	Axiom _2_2_1_b : forall x : OBJECT, exists! t : TYPE, has x TYPE t.

	(* 2.2.1.c - physical description *)

	(* 2.2.1.d-e - ? *)

	(* 2.2.1.f => 3.2.9.c *)

	(* 2.2.1.g-i - ? *)


	(*----------------------*)
	(*   2.2.2 - SUBTYPES   *)
	(*----------------------*)


	(* 2.2.2.a *)
	Axiom SUBTYPE : Type.

	(* 2.2.2.b *)
	Axiom _2_2_2_b : forall x:OBJECT, forall s:SUBTYPE, 
		has x TYPE Hero -> not (has x SUBTYPE s).
	
	(* 2.2.2.c - ntd *)

	(* 2.2.2.d *)
	Variant CHARACTER_SUBTYPE :=
		| Adventurer | Animal | Apprentice | Artist
		| Bureaucrat
		| Citizen | Companion
		| Deity | Dragon | Druid
		| Elemental | Engineer
		| Fairy
		| Leviathan 
		| Mage | Messenger 
		| Noble 
		| Plant 
		| Robot 
		| Soldier | Scholar | Spirit
		| Titan | Trainee
	.
	Axiom character_subtype_is_subtype : CHARACTER_SUBTYPE -> SUBTYPE.
	Coercion character_subtype_is_subtype : CHARACTER_SUBTYPE >-> SUBTYPE.

	Axiom _2_2_2_d : forall x, forall s:CHARACTER_SUBTYPE, 
		has x SUBTYPE s -> has x TYPE Character.

	(* 2.2.2.e *)
	Variant PERMANENT_SUBTYPE :=
		  Landmark
	.
	Axiom permament_subtype_is_subtype : PERMANENT_SUBTYPE -> SUBTYPE.
	Coercion permament_subtype_is_subtype : PERMANENT_SUBTYPE >-> SUBTYPE.

	Axiom _2_2_2_e : forall x, forall s:PERMANENT_SUBTYPE,
		has x SUBTYPE s -> has x TYPE Permanent.

	(* 2.2.2.f *)
	Variant REGION_SUBTYPE :=
		| Forest 
		| Mountain
		| Water
	.
	Axiom region_subtype_is_subtype : REGION_SUBTYPE -> SUBTYPE.
	Coercion region_subtype_is_subtype : REGION_SUBTYPE >-> SUBTYPE.

	Axiom _2_2_2_f : forall x, forall s:REGION_SUBTYPE,
		has x SUBTYPE s -> has x TYPE Region.

	(* 2.2.2.g *)
	Variant SPELL_SUBTYPE :=
		| Boon
		| Conjuration
		| Disruption
		| Maneuver
		| Song
	.
	Axiom spell_subtype_is_subtype : SPELL_SUBTYPE -> SUBTYPE.
	Coercion spell_subtype_is_subtype : SPELL_SUBTYPE >-> SUBTYPE.

	Axiom _2_2_2_g : forall x, forall s:SPELL_SUBTYPE,
		has x SUBTYPE s -> has x TYPE Spell.

	(* 2.2.2.h *)
	Variant EMBLEM_SUBTYPE :=
		| Reaction
		| Ongoing
	.
	Axiom emblem_subtype_is_subtype : EMBLEM_SUBTYPE -> SUBTYPE.
	Coercion emblem_subtype_is_subtype : EMBLEM_SUBTYPE >-> SUBTYPE.

	Axiom _2_2_2_h : forall x, forall s:EMBLEM_SUBTYPE,
		has x SUBTYPE s -> has x TYPE Emblem.

	(* 2.2.2.i - physical description *)

	(* 2.2.2.j - token ? *)

	(* 2.2.2.k *)
	Axiom HeroRegion : OBJECT.
	Axiom CompanionRegion : OBJECT.
	Axiom Arena : OBJECT.
	Axiom _2_2_2_k_HeroRegion :
		has_exactly HeroRegion      SUBTYPE (map region_subtype_is_subtype (Forest :: Mountain :: Water :: nil )).
	Axiom _2_2_2_k_CompanionRegion :
		has_exactly CompanionRegion SUBTYPE (map region_subtype_is_subtype (Forest :: Mountain :: Water :: nil )).
	Axiom _2_2_2_k_Arena : 
		has_exactly Arena           SUBTYPE (map region_subtype_is_subtype (Forest :: Mountain :: Water :: nil )).

	Lemma _2_2_2_k_HeroRegion_is_Region : has HeroRegion TYPE Region.
	Proof. destruct _2_2_2_k_HeroRegion as [[? _] _]. eapply _2_2_2_f. eauto. Qed. 
	Lemma _2_2_2_k_CompanionRegion_is_Region : has CompanionRegion TYPE Region.
	Proof. destruct _2_2_2_k_CompanionRegion as [[? _] _]. eapply _2_2_2_f. eauto. Qed. 
	Lemma _2_2_2_k_Arena_is_Region : has Arena TYPE Region.
	Proof. destruct _2_2_2_k_Arena as [[? _] _]. eapply _2_2_2_f. eauto. Qed. 

	(* 2.2.2.l - ? *)

	(* 2.2.2.m - ? *)

	(* 2.2.2.n-o - ? *)

	(* 2.2.2.p - ? *)


	(*------------------*)
	(*   2.2.3 - NAME   *)
	(*------------------*)

	(* 2.2.3.a *)
	Variant NAME := name : string -> NAME.

	(* 2.2.3.b *)
	Axiom _2_2_3_b : forall x:OBJECT, exists n m:NAME,
		has x NAME n -> has x NAME m -> n = m.

	(* 2.2.3.c-e - physical description *)

	(* 2.2.3.f - token ? *)

	(* 2.2.3.g *)
	Axiom _2_2_3_g : forall x:OBJECT, has x TYPE Emblem -> forall n:NAME, not (has x NAME n).


	(*--------------------*)
	(*   2.2.4 - RARITY   *)
	(*--------------------*)

	(* 2.2.4.a *)
	Variant RARITY :=
		| Common
		| Rare
		| Unique
	.

	(* 2.2.4.b - physical description *)

	(* 2.2.4.c *)
	Axiom _2_2_4_c : forall x:OBJECT, 
		(has x TYPE Hero \/ has x TYPE Region \/ has x TYPE Emblem \/ is_TOKEN x) -> 
		forall r:RARITY, not (has x RARITY r).


	(*---------------------*)
	(*   2.2.5 - VERSION   *)
	(*---------------------*)

	(* TODO *)


	(*-----------------------*)
	(*   2.2.6 - HAND COST   *)
	(*-----------------------*)

	(* 2.2.6.a *)
	Variant HAND_COST := hand_cost : nat -> HAND_COST.

	(* 2.2.6.b - physical description *)

	(* 2.2.6.c *)
	Axiom _2_2_6_c : forall x:OBJECT, is_TOKEN x -> has x HAND_COST (hand_cost 0).

	(* 2.2.6.d *)
	Axiom _2_2_6_d : forall x:OBJECT, has x TYPE Emblem -> forall h:HAND_COST,
		not (has x HAND_COST h).


	(*--------------------------*)
	(*   2.2.7 - RESERVE COST   *)
	(*--------------------------*)

	(* 2.2.7.a *)
	Variant RESERVE_COST := reserve_cost : nat -> RESERVE_COST.

	(* 2.2.7.b - physical description *)

	(* 2.2.7.c *)
	Axiom _2_2_7_c : forall x:OBJECT, is_TOKEN x -> has x RESERVE_COST (reserve_cost 0).

	(* 2.2.7.d *)
	Axiom _2_2_7_d : forall x:OBJECT, has x TYPE Emblem -> forall r:RESERVE_COST,
		not (has x RESERVE_COST r).


	(*---------------------*)
	(*   2.2.8 - FACTION   *)
	(*---------------------*)

	(* 2.2.8.a *)
	Variant FACTION :=
		| Axxiom (* the second x avoids confusion with the word Axiom in Coq *)
		| Bravos
		| Lyra
		| Muna
		| Ordis
		| Yzmir
	.

	(* 2.2.8.b *)
	Definition neutral (x:OBJECT) := forall f:FACTION, not (has x FACTION f).

	(* 2.2.8.c - physical description *)

	(* 2.2.8.d *)
	Axiom _2_2_8_d : forall x:OBJECT, 
		(is_TOKEN x \/ has x TYPE Emblem) -> neutral x.


	(*------------------------*)
	(*   2.2.9 - STATISTICS   *)
	(*------------------------*)

	(* 2.2.9.a-b *)
	Variant STATISTICS := statistics : (REGION_SUBTYPE -> nat) -> STATISTICS. 

	(* 2.2.9.c *)
	Axiom _2_2_9_c : forall x:OBJECT, forall s: STATISTICS,
		has x STATISTICS s -> has x TYPE Character.

	(* 2.2.9.d - physical description *)

	(* 2.2.9.e - token ? *)


	(*------------------------*)
	(*   2.2.10 - ABILITIES   *)
	(*------------------------*)

	(* 2.2.10.a *)
	Variant ABILITIES := (* add "Ability" at the end avoid confusion *)
		| QuickActionAbility
		| ReactionAbility
		| PassiveAbility
		| EffectAbility
	.

	(* 2.2.10.b-c - physical description *)

	(* 2.2.10.d - ? *)

	(* 2.2.10.e - ? *)

	(* 2.2.10.f-g - ? *)

	(* 2.2.10.h-k - ? *)


	(*----------------------------*)
	(*   2.2.11 - RESERVE LIMIT   *)
	(*----------------------------*)

	(* 2.2.11.a *)
	Variant RESERVE_LIMIT := reserve_limit : nat -> RESERVE_LIMIT.

	(* 2.2.11.b *)
	Axiom _2_2_11_b : forall x:OBJECT, forall r:RESERVE_LIMIT,
		has x RESERVE_LIMIT r -> has x TYPE Hero.

	(* 2.2.11.c - physical description *)


	(*-----------------------------*)
	(*   2.2.12 - LANDMARK LIMIT   *)
	(*-----------------------------*)

	(* 2.2.12.a *)
	Variant LANDMARK_LIMIT := landmark_limit : nat -> LANDMARK_LIMIT.

	(* 2.2.12.b *)
	Axiom _2_2_12_b : forall x:OBJECT, forall l:LANDMARK_LIMIT,
		has x LANDMARK_LIMIT l -> has x TYPE Hero.

	(* 2.2.12.c - physical description *)


	(*-----------------------*)
	(*   2.2.13 - DURATION   *)
	(*-----------------------*)

	(* 2.2.13.a *)
	Variant DURATION :=
		| ThisTurn
		| ThisAfternoon
		| ThisDay
	.

	(* 2.2.13.b *)
	Axiom _2_2_13_b : forall x:OBJECT, forall d:DURATION,
		has x DURATION d -> has x SUBTYPE Ongoing.
	Lemma _2_2_13_b' : forall x:OBJECT, forall d:DURATION,
		has x DURATION d -> has x TYPE Emblem.
	Proof. intros. eapply _2_2_2_h. eapply _2_2_13_b. eauto. Qed.

	(* 2.2.13.c - ? *)


	(*------------------------*)
	(*   2.2.14 - TIMESTAMP   *)
	(*------------------------*)

	(* 2.2.14.a *)
	Variant TIMESTAMP := timestamp : nat -> TIMESTAMP.

	(* 2.2.14.c-d - ? *)



	(****************************************)
	(*** 2.3 - APPLYING PASSIVE ABILITIES ***)
	(****************************************)

	(* TODO *)



	(**********************)
	(*** 2.4 - STATUSES ***)
	(**********************)

	(* TODO *)



	(**********************)
	(*** 2.5 - COUNTERS ***)
	(**********************)

	(* 2.5.a-c *)
	Variant COUNTERS := counters : string -> nat -> COUNTERS.

	(* 2.5.d - ? *)

	(* 2.5.e-g - ? *)

	(* 2.5.h - ntd *)

	(* 2.5.i-j - ? *)

	(*----------------------------*)
	(*   2.5.1 - BOOST COUNTERS   *)
	(*----------------------------*)

	(* 2.5.1.a *)
	Definition BoostCounters := counters "boost".

	(* 2.5.1.b - ? *)

End _2_OBJECTS.

Section _3_ZONES.

	(*****************************)
	(*** 3.1 - ZONE PROPERTIES ***)
	(*****************************)

	(*---------------------*)
	(*   3.1.1 - GENERAL   *)
	(*---------------------*)

	(* 3.1.1.a *)
	Axiom ZONE : Type.
	Axiom card_is_in : ZONE -> CARD -> Prop.
	Axiom object_is_in : ZONE -> OBJECT -> Prop.

	(* 3.1.1.c *)
	Variant ZONE_KIND :=
		| Adventure
		| Deck 
		| DicardPile
		| ExpeditionZone
		| Hand 
		| HeroZone 
		| LandmarkZone
		| Limbo
		| ManaZone 
		| Reserve
	(* <= 3.2.4.b *)
		| HeroExpedition
		| CompanionExpedition
	.
	
	Axiom kind : ZONE -> ZONE_KIND.
	Definition has_kind z k := kind z = k.
	Lemma _3_1_1_c : forall z:ZONE, exists! k:ZONE_KIND, has_kind z k.
	Proof. intros. exists (kind z). split; intros; unfold has_kind; auto. Qed.

	(* 3.1.1.b *)
	Axiom _3_1_1_b : forall k:ZONE_KIND, exists z:ZONE, has_kind z k.


	(*-------------------------------*)
	(*   3.1.2 - SHARED OR PRIVATE   *)
	(*-------------------------------*)

	(* 3.1.2.a *)
	Axiom kind_shared : ZONE_KIND -> Prop.
	Definition shared z := kind_shared (kind z).

		(* uniqueness of a shared zone *)
	Axiom _3_1_2_a' : forall z z': ZONE, forall k:ZONE_KIND,
		has_kind z k -> has_kind z' k -> shared z -> z = z'.
	
	Lemma _3_1_2_a : forall k:ZONE_KIND, kind_shared k -> exists! z, has_kind z k.
	Proof.
		intros. destruct _3_1_1_b with k as [z]. exists z. split.
		- auto.
		- intros. eapply _3_1_2_a'; eauto. unfold has_kind in *. subst. auto.
	Qed.

	(* 3.1.2.b *)
	Axiom kind_private k : ZONE_KIND -> Prop.
	Definition private z := kind_private (kind z).
	
	Axiom owner : ZONE -> PLAYER -> Prop.
	Axiom owner_uniqueness : forall z, forall p p', owner z p -> owner z p' -> p = p'.

	Axiom _3_1_2_b : forall k:ZONE_KIND, kind_private k -> forall p, exists! z,
		has_kind z k /\ owner z p.

	Axiom _3_1_2_b_ownership : forall z:ZONE, private z -> exists p:PLAYER, owner z p.
		(* probably provable with a finite number of players ? *)
	
	Lemma _3_1_2_b_ownership' : forall z:ZONE, private z -> exists! p:PLAYER, owner z p.
	Proof.
		intros. edestruct _3_1_2_b_ownership; eauto. eexists. split; eauto. intros. eapply owner_uniqueness; eauto.
	Qed.

	(* 3.1.2.c - ? *)


	(*-------------------------------*)
	(*   3.1.3 - VISIBLE OR HIDDEN   *)
	(*-------------------------------*)

	(* 3.1.3.a *)
	Axiom kind_visible : ZONE_KIND -> Prop.
	Definition visible z := kind_visible (kind z).

	Axiom _3_1_3_a : forall z:ZONE, visible z -> forall c:CARD, not (card_is_in z c).

	(* 3.1.3.b - ? *)

	(* 3.1.3.c - ? *)

	(* 3.1.3.d *)
	Axiom kind_hidden : ZONE_KIND -> Prop.
	Definition hidden z := kind_hidden (kind z). 

	Axiom _3_1_3_d : forall z:ZONE, hidden z ->	forall o:OBJECT, not (object_is_in z o).
	

	(* 3.1.3.e-f - player info ? *)


	(*---------------------*)
	(*   3.1.4 - IN PLAY   *)
	(*---------------------*)

	(* 3.1.4.a *)
	Definition in_play (o:OBJECT) := exists z, object_is_in z o /\
		(has_kind z HeroZone \/ has_kind z ExpeditionZone \/ has_kind z LandmarkZone).



	(*********************************)
	(*** 3.2 - ZONE-SPECIFIC RULES ***)
	(*********************************)

	(*-----------------------*)
	(*   3.2.1 - ADVENTURE   *)
	(*-----------------------*)

	(* 3.2.1.a *)
	Axiom _3_2_1_a  : kind_shared  Adventure.
	Axiom _3_2_1_a' : kind_visible Adventure.

	(* 3.2.1.b-c - ? *)


	(*------------------*)
	(*   3.2.2 - DECK   *)
	(*------------------*)

	(* 3.2.2.a *)
	Axiom _3_2_2_a  : kind_private Deck.
	Axiom _3_2_2_a' : kind_hidden  Deck.

	(* 3.2.2.b-f - ? *)


	(*--------------------------*)
	(*   3.2.3 - DISCARD PILE   *)
	(*--------------------------*)

	(* 3.2.3.a *)
	Axiom _3_2_3_a  : kind_private DicardPile.
	Axiom _3_2_3_a' : kind_visible DicardPile.


	(*-----------------------------*)
	(*   3.2.4 - EXPEDITION ZONE   *)
	(*-----------------------------*)

	(* 3.2.4.a *)
	Axiom _3_2_4_a  : kind_shared  ExpeditionZone.
	Axiom _3_2_4_a' : kind_visible ExpeditionZone.

	(* 3.2.4.b *)
	(* => 3.1.1.c *)
	Axiom subzone : ZONE -> ZONE -> Prop. 
	Notation "z < z'" := (subzone z z'). 

	Axiom _3_2_4_b_hero  : kind_private HeroExpedition.
	Axiom _3_2_4_b_hero' : kind_visible HeroExpedition.
	Axiom _3_2_4_b_hero'' :
		forall z z', has_kind z HeroExpedition -> has_kind z' ExpeditionZone -> z < z'.
	Axiom _3_2_4_b_comp  : kind_private CompanionExpedition.
	Axiom _3_2_4_b_comp' : kind_visible CompanionExpedition.
	Axiom _3_2_4_b_comp'' :
		forall z z', has_kind z CompanionExpedition -> has_kind z' ExpeditionZone -> z < z'.

	(* 3.2.4.c *)
	Lemma _3_2_4_c : forall p, exists z, has_kind z HeroExpedition /\ owner z p.
	Proof. intros. edestruct _3_1_2_b as [z []]; eauto. apply _3_2_4_b_hero. Qed.
	Lemma _3_2_4_c' : forall p, exists z, has_kind z CompanionExpedition /\ owner z p.
	Proof. intros. edestruct _3_1_2_b as [z []]; eauto. apply _3_2_4_b_comp. Qed.

	(* 3.2.4.d-e - ? *)


	(*------------------*)
	(*   3.2.5 - HAND   *)
	(*------------------*)

	(* 3.2.5.a *)
	Axiom _3_2_5_a  : kind_private Hand.
	Axiom _3_2_5_a' : kind_hidden  Hand.

	(* 3.2.5.b-c - ? *)


	(*-----------------------*)
	(*   3.2.6 - HERO ZONE   *)
	(*-----------------------*)
	
	(* 3.2.6.a *)
	Axiom _3_2_6_a  : kind_private HeroZone.
	Axiom _3_2_6_a' : kind_visible HeroZone.

	(* 3.2.6.b *)
	Axiom _3_2_6_b : forall z, has_kind z HeroZone -> forall o o',
		object_is_in z o -> object_is_in z o' -> has o TYPE Hero -> has o' TYPE Hero -> o = o'.


	(*---------------------------*)
	(*   3.2.7 - LANDMARK ZONE   *)
	(*---------------------------*)
	
	(* 3.2.7.a *)
	Axiom _3_2_7_a  : kind_private LandmarkZone.
	Axiom _3_2_7_a' : kind_visible LandmarkZone.


	(*-------------------*)
	(*   3.2.8 - LIMBO   *)
	(*-------------------*)

	(* 3.2.8.a *)
	Axiom _3_2_8_a  : kind_shared  Limbo.
	Axiom _3_2_8_a' : kind_visible Limbo.


	(*-----------------------*)
	(*   3.2.9 - MANA ZONE   *)
	(*-----------------------*)
	
	(* 3.2.9.a *)
	Axiom _3_2_9_a  : kind_private ManaZone.
	Axiom _3_2_9_a' : kind_visible ManaZone.


	(* 3.2.9.b - ? *)

	(* 3.2.9.c | <= 2.1.1.f *)
	Axiom _3_2_9_b : forall z, has_kind z ManaZone -> forall o, object_is_in z o -> has o TYPE ManaOrb.

	(* 3.2.9.d - player info ? *)

	(* 3.2.9.e-f - ? *)


	(*---------------------------*)
	(*   3.2.10 - RESERVE ZONE   *)
	(*---------------------------*)
	
	(* 3.2.10.a *)
	Axiom _3_2_10_a  : kind_private Reserve.
	Axiom _3_2_10_a' : kind_visible Reserve.

	

	Lemma _3_2_no_cards_and_objects : forall z:ZONE, 
		not (exists c:CARD, exists o:OBJECT, card_is_in z c /\ object_is_in z o).
	Proof.
		intros z H. destruct H as [c [o []]].
		destruct _3_1_1_c with z as [k [Hk _]].
		induction k.
		- edestruct _3_1_3_a; eauto. unfold visible. rewrite Hk. apply _3_2_1_a'.
		- edestruct _3_1_3_d; eauto. unfold hidden.  rewrite Hk. apply _3_2_2_a'.
		- edestruct _3_1_3_a; eauto. unfold visible. rewrite Hk. apply _3_2_3_a'.
		- edestruct _3_1_3_a; eauto. unfold visible. rewrite Hk. apply _3_2_4_a'.
		- edestruct _3_1_3_d; eauto. unfold hidden.  rewrite Hk. apply _3_2_5_a'.
		- edestruct _3_1_3_a; eauto. unfold visible. rewrite Hk. apply _3_2_6_a'.
		- edestruct _3_1_3_a; eauto. unfold visible. rewrite Hk. apply _3_2_7_a'.
		- edestruct _3_1_3_a; eauto. unfold visible. rewrite Hk. apply _3_2_8_a'.
		- edestruct _3_1_3_a; eauto. unfold visible. rewrite Hk. apply _3_2_9_a'.
		- edestruct _3_1_3_a; eauto. unfold visible. rewrite Hk. apply _3_2_10_a'.
		- edestruct _3_1_3_a; eauto. unfold visible. rewrite Hk. apply _3_2_4_b_hero'.
		- edestruct _3_1_3_a; eauto. unfold visible. rewrite Hk. apply _3_2_4_b_comp'.
	Qed.

End _3_ZONES.

Section _4_GAME_PROGRESSION.

	Axiom ATOMIC_ACTION : Type.

	Axiom STEP : Type.
	Axiom step_atomic_actions : STEP -> list ATOMIC_ACTION -> Prop.
	Axiom step_atomic_actions_unique : forall s aas aas', step_atomic_actions s aas -> step_atomic_actions s aas' -> aas = aas'.

	Definition SEQUENCE := list STEP.

	Axiom EFFECT : Type.
	Axiom effect_sequence : EFFECT -> SEQUENCE -> Prop.
	Axiom effect_sequence_unique : forall e s s', effect_sequence e s -> effect_sequence e s' -> s = s'.

	Axiom PLAYER_ACTION : Type.

	Variant ACTION :=
		| Effect : EFFECT -> ACTION
		| Step : STEP -> ACTION
		| AtomicAction : ATOMIC_ACTION -> ACTION
		| PlayerAction : PLAYER_ACTION -> ACTION
		| CheckReactions
	.
	Notation "#{ a }" := (AtomicAction a).

	Axiom new_day : ATOMIC_ACTION.


	Axiom GAME_STATE : Type.
	Definition ACTION_STACK := list ACTION.
	Variant GAME_PENDING := game_pending : GAME_STATE -> ACTION_STACK -> GAME_PENDING. 
	Notation "s @ G" := (game_pending G s) (at level 80).

	Axiom perform : GAME_PENDING -> GAME_PENDING -> Prop.
	Notation "p ~> p'"             := ( perform p p' )                           (at level 90).
	Notation "G ~( a |  s )~> G'"  := ( (a::s) @ G ~> s @ G' )                   (at level 90).
	Notation "G ~( a |>> s )~> G'" := ( forall s', (a::s') @ G ~> (s++s') @ G' ) (at level 90).
	Notation "G ~( a |> a' )~> G'" := ( G ~( a |>> (a' :: nil) )~> G' )          (at level 90).
	Notation "G ~( a )~> G'"       := ( forall s, G ~( a | s )~> G' )            (at level 90).
	Notation "~( a |>> s )"         := ( forall G, G ~( a |>> s )~> G )           (at level 90).
	Notation "~( a |> a' )"         := ( forall G, G ~( a |> a' )~> G )           (at level 90).
	Notation "~( a | )"             := ( forall G, G ~( a )~> G )                 (at level 90).


	Axiom perform_effect : forall e sq,
		effect_sequence e sq -> ~( Effect e |>> map Step sq ).

	Axiom perform_step : forall s aas,
		step_atomic_actions s aas -> ~( Step s |>> (map AtomicAction aas) ++ (CheckReactions :: nil) ).
	

	(***********************************)
	(*** 4.1 - BEGINNING OF THE GAME ***)
	(***********************************)

	(* TODO *)



	(****************************)
	(*** 4.2 - DAY STRUCTURE  ***)
	(****************************)

	(* 4.2.a *)
	Variant PHASE :=
		| Morning
		| Noon 
		| Afternoon 
		| Dusk
		| Night
	.

	Axiom begin_phase : PHASE -> ATOMIC_ACTION.
	Axiom play_phase  : PHASE -> ATOMIC_ACTION.
	Axiom end_phase   : PHASE -> ATOMIC_ACTION.

	(* 4.2.b => *)

	(* 4.2.c *)
	Axiom DAILY_EFFECT : Type.
	Axiom daily_effect_is_effect : DAILY_EFFECT -> EFFECT.
	Coercion daily_effect_is_effect : DAILY_EFFECT >-> EFFECT.

	Axiom daily_effects : PHASE -> list DAILY_EFFECT -> Prop.
	Definition daily_effects_as_actions := map (fun de => Effect (daily_effect_is_effect de)).

	(* 4.2.d - ntd *)

	Axiom _4_2 : forall ph es, daily_effects ph es ->
		~( #{ begin_phase ph } |>>
			CheckReactions :: (daily_effects_as_actions es) ++ #{ play_phase ph } :: #{ end_phase ph } :: nil
		).


	(*---------------------*)
	(*   4.2.1 - MORNING   *)
	(*---------------------*)

	(* 4.2.1.a => *)

	(* 4.2.1.b *)
	Axiom Suceed : DAILY_EFFECT.
	(* ? *)

	(* 4.2.1.c *)
	Axiom Prepare : DAILY_EFFECT.
	(* ? *)

	(* 4.2.1.d *)
	Axiom Draw : DAILY_EFFECT.
	(* ? *)

	(* 4.2.1.e *)
	Axiom Expand : DAILY_EFFECT.
	(* ? *)

	(* <= 4.2.1.a *)
	Axiom _4_2_1_a : daily_effects Morning (Suceed :: Prepare :: Draw :: Expand :: nil).

	Axiom _4_2_1_play : ~( #{ play_phase Morning } | ).
	Axiom _4_2_1_end  : ~( #{ end_phase Morning } |> #{ begin_phase Noon }).


	(*------------------*)
	(*   4.2.2 - NOON   *)
	(*------------------*)

	(* 4.2.2.a *)
	Axiom _4_2_2_a : daily_effects Noon nil.

	Axiom _4_2_2_play : ~( #{ play_phase Noon } | ).
	Axiom _4_2_2_end  : ~( #{ end_phase Noon } |> #{ begin_phase Afternoon }).


	(*-----------------------*)
	(*   4.2.3 - AFTERNOON   *)
	(*-----------------------*)

	Axiom _4_2_3_daily_effects : daily_effects Afternoon nil.

	(* todo *)

	Axiom _4_2_3_end  : ~( #{ end_phase Afternoon } |> #{ begin_phase Dusk }).

	(*------------------*)
	(*   4.2.4 - DUSK   *)
	(*------------------*)

	(* 4.2.4.a => *)

	(* 4.2.4.b-e - ?*)
	Axiom Progress : DAILY_EFFECT.
	(* ? *)

	Axiom _4_2_4_a : daily_effects Dusk (Progress :: nil).

	
	Axiom _4_2_4_play : ~( #{ play_phase Dusk } | ).
	Axiom _4_2_4_end  : ~( #{ end_phase Dusk } |> #{ begin_phase Night }).

	(*-------------------*)
	(*   4.2.5 - NIGHT   *)
	(*-------------------*)

	(* 4.2.5.a => *)

	(* 4.2.5.b *)
	Axiom Rest : DAILY_EFFECT.
	(* ? *)

	(* 4.2.5.c *)
	Axiom CleanUp : DAILY_EFFECT.
	(* ? *)
	(* 4.2.5.d - ? *)

	(* <= 4.2.5.a *)
	Axiom _4_2_5_a : daily_effects Night (Rest :: CleanUp :: nil).

	Axiom _4_2_5_play : ~( #{ play_phase Night } | ).
	Axiom _4_2_5_end  : ~( #{ end_phase Dusk } |> #{ new_day }).


End _4_GAME_PROGRESSION.
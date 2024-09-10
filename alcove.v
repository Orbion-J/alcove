Require Import List.
Require Import String.

Module _2_OBJECTS.

	Axiom OBJECT : Type.

	(*****************************)
	(*   2.2 - CHARACTERISTICS   *)
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
		| Permanent 
		| Region
		| Spell
	.

	(* 2.2.1.b *)
	Axiom _2_2_1_b : forall x : OBJECT, exists! t : TYPE, has x TYPE t.

	(* 2.2.1.c - physical description *)

	(* 2.2.1.d-g - ? *)

	(* 2.2.1.h - ? *)

	(* 2.2.1.i - ? *)


	(*----------------------*)
	(*   2.2.2 - SUBTYPES   *)
	(*----------------------*)

	Axiom SUBTYPE : Type.

	(* 2.2.2.a - ntd *)

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

	(* 2.2.2.j - ntd ? *)

	(* 2.2.2.k *)
	Axiom HeroRegion : OBJECT.
	Axiom CompanionRegion : OBJECT.
	Axiom Arena : OBJECT.
	Axiom _2_2_2_k_HeroRegion : has_exactly HeroRegion SUBTYPE (map region_subtype_is_subtype (Forest :: Mountain :: Water :: nil )).
	Axiom _2_2_2_k_CompanionRegion : has_exactly CompanionRegion SUBTYPE (map region_subtype_is_subtype (Forest :: Mountain :: Water :: nil )).
	Axiom _2_2_2_k_Arena : has_exactly Arena SUBTYPE (map region_subtype_is_subtype (Forest :: Mountain :: Water :: nil )).

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
	Definition NAME := string.

	(* 2.2.3.b *)
	Axiom _2_2_3_b : forall x:OBJECT, exists n m:NAME,
		has x NAME n -> has x NAME m -> n = m.

	(* 2.2.3.c-e - physical description *)

	(* 2.2.3.f - ? *)

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

	(* 2.2.9.e - ? *)


	(*------------------------*)
	(*   2.2.10 - ABILITIES   *)
	(*------------------------*)

	(* 2.2.10.a *)
	Variant ABILITIES := 
		| QuickAction
		| ReactionAbility (* not name Reaction to avoid confusion with the subtype *)
		| PassiveAbility
		| Effect
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


End _2_OBJECTS.
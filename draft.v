Module Player.

	Variant Player :=
	| Alice : Player
	| Bob : Player 
	.

	Definition nextPlayer (p :Player) : Player :=
	match p with
	| Alice => Bob
	| Bob => Alice
	end.

	Definition each (T:Type) := Player -> T.

	Definition foreach P := P Alice /\ P Bob.

End Player.

Module Biome.

	Variant Biome :=
	| Forest 
	| Mountain
	| Ocean 
	.

End Biome.


Require Import String.

Module Card.

	Variant Rarity :=
	| Common : Rarity
	| Rare : Rarity
	| Unique : Rarity
	.

	Variant Faction :=
	| Axxiom : Faction (* the second x avoids confusion with the word Axiom in Coq*)
	| Bravos : Faction
	| Lyra : Faction
	| Muna : Faction
	| Ordis : Faction
	| Yzmir : Faction
	.

	Variant CardType :=
	| Character
	| Spell
	| Permanent
	| Hero
	.

	Variant CardSubtype :=
	| XX : CardSubtype
	.

	Definition Statistics := Biome.Biome -> nat.

	
	Variant Ability := (* TODO *)
	| ActivatedAbility
	| PassiveAbility
	| TriggeredAbility
	.

	Record Card :=
	{
		name : string ;
		faction : Faction ;
		rarity : Rarity ;
		type : CardType ;
		subtype : CardSubtype ;
		handCost : nat ;
		reserveCost : nat ;
		statistics : option Statistics ;
		abilities : list Ability
	}.

	Definition Counter := prod string nat .

	Variant Properties :=
	| Asleep
	| Anchored
	| Fleeting
	. 
	
	Record OnBordCard :=
	{
		card : Card ;

		exhausted : bool ;

		boosts : nat ;
		counters : list Counter ;

		properties : Properties -> bool ;

		faceUp : bool ;
	}.

	Definition HeroCard := exists c : OnBordCard, c.(card).(type) = Hero.

End Card.


Module Tumult.

	Import Biome.

	Definition Region := Biome -> bool.
	
	Definition regionFMO : Region := fun (b:Biome) => true.
	Definition regionF : Region := fun b => match b with Forest => true | _ => false end.
	Definition regionM : Region := fun b => match b with Mountain => true | _ => false end.
	Definition regionO : Region := fun b => match b with Ocean => true | _ => false end.
	Definition regionFM : Region := fun b => match b with Ocean => false | _ => true end.
	Definition regionMO : Region := fun b => match b with Forest => false | _ => true end.
	Definition regionFO : Region := fun b => match b with Mountain => false | _ => true end.

	Definition UnorientedTumultCard := Biome. (* the lonely biome of the card *)
	Record TumultCard := {
		card : UnorientedTumultCard ;
		orientation : bool ; (* true : the lonely biome is left *)
		revealed : bool ;
	}.
	
	Variant allBiomes : Biome -> Biome -> Biome -> Prop :=
	| allBiomes_FMO : allBiomes Forest Mountain Ocean
	| allBiomes_FOM : allBiomes Forest Ocean Mountain
	| allBiomes_MFO : allBiomes Mountain Forest Ocean
	| allBiomes_MOF : allBiomes Mountain Ocean Forest
	| allBiomes_OFM : allBiomes Ocean Forest Mountain
	| allBiomes_OMF : allBiomes Ocean Mountain Forest
	. 

	Variant TumultLane := 
	| TumultLane_cons : forall t1 t2 t3 : TumultCard,
		allBiomes t1.(card) t2.(card) t3.(card) -> TumultLane
	.

End Tumult.		


Module Days.


	Variant MorningStep :=
	| Setup
	| FirstPlayerDraw
	| SecondPlayerDraw
	.

	Definition compareMorningSteps (s1 s2 : MorningStep) :=
	match s1, s2 with
	| Setup, Setup => Eq 
	| Setup, _ => Lt 
	| FirstPlayerDraw, Setup => Gt 
	| FirstPlayerDraw, FirstPlayerDraw => Eq 
	| FirstPlayerDraw, SecondPlayerDraw => Lt 
	| SecondPlayerDraw, SecondPlayerDraw => Eq 
	| SecondPlayerDraw, _ => Gt 
	end.

	Variant NightStep :=
	| Rest 
	| Cleanup
	.

	Definition compareNightSteps (s1 s2 : NightStep) :=
	match s1, s2 with 
	| Rest, Rest => Eq
	| Rest, _ => Lt 
	| Cleanup, Cleanup => Eq 
	| Cleanup, _ => Gt 
	end.


	Record PassingPlayers := {
		first : bool ;
		second : bool ;
	}.

	Record Turn := {
		player : Player.Player ;
		turnNumber : nat ;
	}.

	Definition compareTurns (t1 t2 : Turn) := Nat.compare t1.(turnNumber) t2.(turnNumber).

	Variant Phase :=
	| Morning : MorningStep -> Phase
	| Noon
	| Afternoon : Turn -> PassingPlayers -> Phase
	| Dusk
	| Night : NightStep -> Phase
	.

	Definition comparePhases (p1 p2 : Phase) :=
	match p1, p2 with 
	| Morning s1, Morning s2 => compareMorningSteps s1 s2
	| Morning _, _ => Lt 
	| Noon, Morning _ => Gt
	| Noon, Noon => Eq 
	| Noon, _ => Lt
	| Afternoon _ _ , Morning _ => Gt
	| Afternoon _ _ , Noon => Gt
	| Afternoon t1 _ , Afternoon t2 _ => compareTurns t1 t2
	| Afternoon _ _ , _ => Lt
	| Dusk, Dusk => Eq 
	| Dusk, Night _ => Lt 
	| Dusk, _ => Gt 
	| Night s1, Night s2 => compareNightSteps s1 s2
	| Night _, _ => Gt 
	end.

	Record Day := {
		firstPlayer : Player.Player ;
		dayNumber : nat ;
		phase : Phase ;
	}.
	
	Definition compareDays (d1 d2 : Day) :=
	match Nat.compare d1.(dayNumber) d2.(dayNumber) with
	| Lt => Lt 
	| Gt => Gt 
	| Eq => comparePhases d1.(phase) d2.(phase)
	end.


	Notation "D << D'" := (compareDays D D') (at level 50).



	Lemma compareNightSteps_antisym : forall S S', compareNightSteps S S' = CompOpp (compareNightSteps S' S).
	Proof. intros. destruct S; destruct S'; auto. Qed.
	Lemma compareMorningSteps_antisym : forall S S', compareMorningSteps S S' = CompOpp (compareMorningSteps S' S).
	Proof. intros. destruct S; destruct S'; auto. Qed.
	Lemma comparePhases_antisym : forall P P', comparePhases P P' = CompOpp( comparePhases P' P ).
	Proof.
		intros. destruct P ; destruct P'; auto; unfold compareDays; simpl.
		- apply compareMorningSteps_antisym.	
		- unfold compareTurns. apply PeanoNat.Nat.compare_antisym.
		- apply compareNightSteps_antisym.
	Qed.
	Lemma compareDays_antisym : forall D D', D << D' = CompOpp (D' << D).
	Proof.
		intros. destruct D. destruct D'. 
		destruct (Compare_dec.lt_eq_lt_dec dayNumber0 dayNumber1) as [[]|];
		unfold compareDays; simpl. 
		- assert (Nat.compare dayNumber0 dayNumber1 = Lt) by (apply PeanoNat.Nat.compare_lt_iff; auto).
		  assert (Nat.compare dayNumber1 dayNumber0 = Gt) by (apply PeanoNat.Nat.compare_gt_iff; auto). 
		  rewrite H, H0; auto.
		- assert (Nat.compare dayNumber0 dayNumber1 = Eq) by (apply PeanoNat.Nat.compare_eq_iff; auto).
		  assert (Nat.compare dayNumber1 dayNumber0 = Eq) by (apply PeanoNat.Nat.compare_eq_iff; auto). 
		  rewrite H, H0; auto.
		  apply comparePhases_antisym.
		- assert (Nat.compare dayNumber1 dayNumber0 = Lt) by (apply PeanoNat.Nat.compare_lt_iff; auto).
		  assert (Nat.compare dayNumber0 dayNumber1 = Gt) by (apply PeanoNat.Nat.compare_gt_iff; auto). 
		  rewrite H, H0; auto.
	Qed.


End Days.

Module GameState.

	Definition Expedition := list Card.OnBordCard .

	Record GameState :=
	{
		day : Days.Day ;

		hands :  (list Card.Card) ;

		decks : Player.each (list Card.Card) ;

		heroes : Player.each Card.HeroCard ;

		tumult : Tumult.TumultLane ;
		tieBreaker : bool ;
		heroToken : Player.each nat ; (* number of steps from the start *)
		companionToken : Player.each nat ; (* idem *)

		heroExpeditions : Player.each Expedition ;
		companionExpeditions : Player.each Expedition ;

		reserves : Player.each (list Card.OnBordCard) ;
		landmarks : Player.each (list Card.OnBordCard) ;

		mana : Player.each (list Card.OnBordCard) ;

	}.

	Definition _win (p:Player.Player) (G:GameState) :=
		(tieBreaker G = false) /\ (heroToken G p + companionToken G p >= 7).

	Import Card.

	Fixpoint foreach {T:Type} (P:T -> Prop) (xs:list T) := 
	match xs with 
	| nil => True
	| cons x xs => (P x) /\ foreach P xs
	end.

	Definition manaValidOneCard (c:OnBordCard) := c.(faceUp) = false.
	Definition manaValidOnePlayer G p := foreach manaValidOneCard (mana G p).
	Definition manaValid G := Player.foreach (manaValidOnePlayer G).
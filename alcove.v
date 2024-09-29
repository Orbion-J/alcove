Require Import List.
Require Import String.
Require Import Lia.
Require Import Nat.

From RecordUpdate Require Import RecordSet.
Import RecordSetNotations.


Module Utils.

	Notation "l +: s" := (l ++ (s :: nil)) (at level 80).

End Utils.
Import Utils.

Module PLAYER.

	Axiom PLAYERS : Type.

	Axiom PLAYER : Type.

	Axiom next_player : PLAYER -> PLAYER.

	Axiom all : PLAYERS -> Prop.
	Axiom not_all : PLAYERS -> Prop.

	Axiom next_player_condition : (PLAYER -> Prop) -> PLAYER -> PLAYER.
 
	Axiom among : PLAYERS -> PLAYER -> Prop.

	Axiom none : PLAYERS.

	Axiom add : PLAYER -> PLAYERS -> PLAYERS.

End PLAYER.


Module CARD.

	Axiom CARD : Type.

End CARD.

Module ZONE.

	Axiom ZONE : Type.

End ZONE.

Module TIME.

	(******************)
	(*** TIMESTAMPS ***)
	(******************)

	Definition TIMESTAMP := nat.
	Definition new_timestamp : TIMESTAMP -> TIMESTAMP := fun t => S t.


	(**********************)
	(*** GAME STRUCTURE ***)
	(**********************)

	Definition DAY := nat.
	Definition next_day : DAY -> DAY := fun d => S d.

	(*********************)
	(*** DAY STRUCTURE ***)
	(*********************)

	Variant PHASE :=
		| Morning
		| Noon 
		| Afternoon 
		| Dusk
		| Night
	.

	Definition next_phase : PHASE -> PHASE := fun ph => match ph with
		| Morning => Noon 
		| Noon => Afternoon 
		| Afternoon => Dusk
		| Dusk => Night
		| Night => Morning
	end.

	(**********************)
	(*** TURN STRUCTURE ***)
	(**********************)

	Record TURN := mkTURN {
		turn_number : nat ;
		active_player : PLAYER.PLAYER ;
		passing_players : PLAYER.PLAYERS ;
	}.

	Instance etaTURN : Settable _ := settable! mkTURN <turn_number; active_player; passing_players>.

	Definition next_turn (t:TURN) :=
		t <| turn_number ::= S |>
		  <| active_player ::=
		  	PLAYER.next_player_condition (PLAYER.among (passing_players t)) |>.

	Definition first_turn (p:PLAYER.PLAYER) : TURN := {|
		turn_number := 0 ;
		active_player := p ;
		passing_players := PLAYER.none ;
	|}.

End TIME.



Module GAME_CONFIGURATION.

	(* PLAYERS *)
	Record CFG_PLAYERS := mkCFG_PLAYERS {
		all : PLAYER.PLAYERS ;
		first : PLAYER.PLAYER ;
	}.

	Instance etaCFG_PLAYERS : Settable _ := settable! mkCFG_PLAYERS <all;first>.
	

	(* ZONES *)
	Record CFG_ZONES := mkCFG_ZONES {
	}.
	(* Instance etaCFG_ZONES : Settable _ := settable! mkCFG_ZONES < >. *)

	(* TIME *)
	Record CFG_TIME := mkCFG_TIME {
		last_timestamp : TIME.TIMESTAMP ;
		day : TIME.DAY ;
		phase : TIME.PHASE ;
		turn : TIME.TURN ;
	}.
	Instance etaCFG_TIME : Settable _ := settable! mkCFG_TIME <last_timestamp;day;phase;turn>.


	(* GAME CONFIGURATION *)
	Record GAME_CONFIGURATION := mkGC {
		players : CFG_PLAYERS ;

		zones : CFG_ZONES ;
		
		time : CFG_TIME ;
	}.
	
	Instance etaGC : Settable _ := settable! mkGC <players;zones;time>.



End GAME_CONFIGURATION.


Module ACTION.

	(**********************)
	(*** ATOMIC ACTIONS ***)
	(**********************)
	
	Variant ATOMIC_ACTION :=
		(* day structure *)
		| new_day
		| begin_phase
		| play_phase
		| end_phase

		(* turn structure *)
		| begin_turn
		| play_turn
		| end_turn
	.


	(*************)
	(*** STEPS ***)
	(*************)

	Record STEP := {
		step_atomic_actions : list ATOMIC_ACTION ;
	}.

	Definition SEQUENCE := list STEP.


	(***************)
	(*** EFFECTS ***)
	(***************)

	Record EFFECT := {
		effect_sequence : SEQUENCE ;
	}.

	
	(*-----------------*)
	(*  DAILY EFFECTS  *)
	(*-----------------*)

	(* Morning *)
	Axiom Suceed : EFFECT.
	Axiom Prepare : EFFECT.
	Axiom Draw : EFFECT.
	Axiom Expand : EFFECT.

	(* Dusk *)
	Axiom Progress : EFFECT.
	
	(* Night *)
	Axiom Rest : EFFECT.
	Axiom CleanUp : EFFECT.
	

	Definition daily_effects (ph:TIME.PHASE) : list EFFECT := match ph with 
		| TIME.Morning => Suceed :: Prepare :: Draw :: Expand :: nil
		| TIME.Noon => nil
		| TIME.Afternoon => nil
		| TIME.Dusk => Progress :: nil
		| TIME.Night => Rest :: CleanUp :: nil
	end.


	(**********************)
	(*** PLAYER ACTIONS ***)
	(**********************)

	Inductive PLAYER_ACTION :=
		| Choice : list PLAYER_ACTION -> PLAYER_ACTION
		| Pass 
		| PlayCard
		| PlayQuickAction
	.


	(***************)
	(*** ACTIONS ***)
	(***************)

	Variant ACTION :=
		| Effect : EFFECT -> ACTION
		| Step : STEP -> ACTION
		| AtomicAction : ATOMIC_ACTION -> ACTION
		| PlayerAction : PLAYER.PLAYER -> PLAYER_ACTION -> ACTION
		| CheckReactions
	.
	Notation "#{ a }" := (AtomicAction a).

	Definition actions_from_effect (e:EFFECT) : list ACTION :=
		map Step (effect_sequence e).

	Definition actions_from_step (s:STEP) : list ACTION :=
		map AtomicAction (step_atomic_actions s).

	Definition actions_from_daily_effects (ph:TIME.PHASE) : list ACTION :=
		map Effect (daily_effects ph).


	(********************)
	(*** ACTION STACK ***)
	(********************)

	Definition ACTION_STACK := list ACTION.


End ACTION. 

Module GAME_PROGRESSION.

	Import GAME_CONFIGURATION.
	Import TIME.
	Import ACTION.


	Variant GAME_PENDING := game_pending : GAME_CONFIGURATION -> ACTION_STACK -> GAME_PENDING. 
	Notation "s @ G" := (game_pending G s) (at level 80).


	Reserved Notation "p ~> p'"             (at level 90).
	Reserved Notation "G ~( a | s )~> G'"   (at level 90).
	Reserved Notation "G ~( a |>> s )~> G'" (at level 90).
	Reserved Notation "G ~( a |> a' )~> G'" (at level 90).
	Reserved Notation "G ~( a )~> G'"       (at level 90).
	Reserved Notation "~( a |>> s )"        (at level 90).
	Reserved Notation "~( a |> a' )"        (at level 90).
	Reserved Notation "~( a | )"            (at level 90).


	Inductive progress : GAME_PENDING -> GAME_PENDING -> Prop :=
		(* Actions *)
		| progress_effect : forall e,
			~( Effect e |>> actions_from_effect e )

		| progress_step : forall s,
			~( Step s |>> actions_from_step s +: CheckReactions )

		(* | progress_check_reactions : ? *)

			(* Player actions <*)

			(* Atomic actions <*)

				(* Day structure aa *)
		| progress_aa_new_day : forall G, 
			G ~( #{ new_day } |> #{ begin_phase })~>
				G <| time;day ::= TIME.next_day |> <| time;phase := TIME.Morning |>

		| progress_aa_begin_phase : forall G,
			G ~( #{ begin_phase } |>>
				CheckReactions ::
				( actions_from_daily_effects G.(time).(phase) ) ++ 
				#{ play_phase } :: #{ end_phase } :: nil
			)~> G

		| progress_aa_end_phase_not_night : forall G, G.(time).(phase) <> TIME.Night ->
			G ~( #{ end_phase } |> #{ begin_phase })~>
				G <| time;phase ::= TIME.next_phase |>

		| progress_aa_end_phase_night : forall G, G.(time).(phase) = TIME.Night ->
			G ~( #{ end_phase } |> #{ new_day } )~> G
		
		| progress_aa_play_phase_not_afternoon : forall G, G.(time).(phase) <> TIME.Afternoon ->
			G ~( #{ play_phase } )~> G

		| progress_aa_play_phase_afternoon : forall G, G.(time).(phase) = TIME.Afternoon ->
			G ~( #{ play_phase } |> #{ begin_turn } )~>
				G <| time;turn := (TIME.first_turn (G.(players).(first))) |>

				(* Turn structure aa *)
		| progress_aa_begin_turn : forall G,
			G ~( #{ begin_turn } |>
				PlayerAction (G.(time).(turn).(active_player)) (Choice (Pass :: PlayCard :: PlayQuickAction :: nil ))
			)~> G

		| progress_aa_end_turn_all_pass : forall G, PLAYER.all G.(time).(turn).(passing_players) ->
			G ~( #{ end_turn } |> #{ end_phase })~> G

		| progress_aa_end_turn_not_all_pass : forall G, PLAYER.not_all G.(time).(turn).(passing_players) ->
			G ~( #{ end_turn } |> #{ begin_turn } )~> G <| time;turn ::= TIME.next_turn |>
		
		
		| progress_pa_pass : forall p, forall G,
			G ~( PlayerAction p Pass |>> CheckReactions :: #{ end_turn } :: nil )~>
				G <| time;turn;passing_players ::= PLAYER.add p |>

		| progress_pa_play_card : forall p, forall G,
			G ~( PlayerAction p PlayCard |>>
				(* TODO ++ *) CheckReactions :: #{ end_turn } :: nil )~> G 

		| progress_pa_play_quick_action : forall p, forall G,
			G ~( PlayerAction p PlayQuickAction |>>
				(* TODO ++ *) CheckReactions :: #{ begin_turn } :: nil )~> G 
	

	where "p ~> p'"           := ( progress p p' )
	and "G ~( a | s )~> G'"   := ( (a::s) @ G ~> s @ G' ) 
	and "G ~( a |>> s )~> G'" := ( forall s', (a::s') @ G ~> (s++s') @ G' ) 
	and "G ~( a |> a' )~> G'" := ( G ~( a |>> (a' :: nil) )~> G' )
	and "G ~( a )~> G'"       := ( forall s, G ~( a | s )~> G' )
	and "~( a |>> s )"        := ( forall G, G ~( a |>> s )~> G )
	and "~( a |> a' )"        := ( forall G, G ~( a |> a' )~> G )
	and "~( a | )"            := ( forall G, G ~( a )~> G ).

End GAME_PROGRESSION.
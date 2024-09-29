# AlCoVe - Altered Coq Verification

AlCoVe (for Altered Coq Verification) is a project of formal verification in Coq
of the rules of the game Altered.

## Goals

This project aims to provide a [Coq](https://coq.inria.fr/) implementation of the [Altered](https://www.altered.gg) [Comprehensive Rules](https://altered-prod-eu.s3.eu-west-3.amazonaws.com/downloads/comprehensive-rules/2024_Altered_TCG_Comprehensive_Rules_1.0_EN.pdf)
(CompRules).
This has several objectives :
- First, a complete implementation of the CompRules will show that the rules can indeed be formalized unambiguously
- It would allow to detect any loophole in the rules
- It would provide a tool to resolve rules questions with high confidence (but also kind of hard work if it needs an intricate proof)
- It will also provide tools to formally verify actual implementations of the game such as the [Board Game Arena game](https://fr.boardgamearena.com/gamepanel?game=altered) or [ExAltered](https://wrong-timeline.itch.io/exaltered) to detect and prevent rule bugs.
- Whence the tool will be mature, it could also be used to create an app that automatically answer rule questions.


## Coq

> Coq is a formal proof management system. It provides a formal language to write mathematical definitions, executable algorithms and theorems together with an environment for semi-interactive development of machine-checked proofs. Typical applications include the certification of properties of programming languages (e.g. the CompCert compiler certification project, the Verified Software Toolchain for verification of C programs, or the Iris framework for concurrent separation logic), the formalization of mathematics (e.g. the full formalization of the Feit-Thompson theorem, or homotopy type theory), and teaching. *(excerpt from Coq website)*
	

## Contribution

This project is initially developed by Orbion but anyone that is willing to help is
invited to get involved. You can reach me directly or open issues or PRs.


## Licence

This is an open source project, feel free to use this work in your own project. Please read
the `LICENCE` file before doing so or fore more information.

## Dependancies

- Coq record update : https://github.com/tchajed/coq-record-update 
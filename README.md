# 591-tla-final
Final Project for EECS 591

TLA specifications can be found in the master branch. Here are short descriptions of each spec:

TCommit.tla: Baseline transaction commit spec taken from Lamport's Github page

TwoPhaseOG.tla: The original 2PC spec without liveness taken from Lamport's Github page.

MidPointTwoPhaseLive.tla: Our in-progress attempt at adding liveness to 2PC at the time of the midpoint presentation.

TwoPhaseWithLivenessFinal.tla: Our final implementation of 2PC including a liveness constraint. Tested in TLA model checker using 6 RMs.

ThreePhase.tla: Our final implementation of 3PC with including a liveness constraint. Tested in TLA model checker using 7 RMs.

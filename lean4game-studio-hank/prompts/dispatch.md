# Dispatch

The rig has already read `pipeline-state.json` and written the active codon ID to `active-codon.txt`. Your only job is to confirm this happened correctly.

Read `active-codon.txt` and `pipeline-state.json`.

If `active-codon.txt` contains `done`, write "PIPELINE_COMPLETE" and stop.

Otherwise, write a one-line status: "Iteration dispatching to: {codon-id} | Course: {currentCourse} | World: {currentWorld} | Review round: {reviewRound}"

Do not modify any files. Do not change pipeline-state.json. Do not change active-codon.txt. The rig already did the work.

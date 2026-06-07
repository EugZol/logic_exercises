# Logic exercises

A set of logic exercises. Covered topics:

* Hilbert-style intuitionistic logic (`IntHilbert.lean`)
* Gentzen-style intuitionistic logic (`IntGentzExercises.lean`)

Quickstart: run the dev container, replace `exercise` terms with your solutions in `*Exercises.lean` files.

## Devcontainer

VS code devcontainer is available, run with Ctrl+Shift+P, "Reopen in container".

## Exercises

To solve exercises, open `<something>Exercises.lean` files. The corresponding `<something>.lean` file would contain full solutions, so don't look into it unless you want spoilers.

### Regenerate exercises

Run `python3 scripts/make_exercises.py LogicExercises/Int.lean`. This writes the sibling `LogicExercises/IntExercises.lean` file.

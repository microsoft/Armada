# Multilevel Editor for Starmada

There are two modes for this Starmada Code Refactoring tool: step-by-step mode, similar to the git workflow, used by GUI; and one-pass mode, used in CLI.

## Workflow (step-by-step mode)

Four verbs are provided: `backup`, `extract`, `apply` and `restore`. 

### Backup

Clean `.build` and duplicate the current project. Effectively `cp -f`.

### Extract

Given a caret position, extract information for the refactor process. Needs most of the user's input.

### Apply

Apply the refactor from candidates.

### Restore

Restore the old project if something went wrong. Clean current project and restore previous state.

## Command Line Interface (one-pass mode)

```
./Binary/Editor shoot {proj_root} -o {dump} -f {caret_file} -p {caret_position} -m {output_mode} -c {check_mode} < {refactor_candidate_file}
```

Where

- `{proj_root}` - The root of a Starmada project, containing all the `.arm` files.
- `{dump}` - A proposed project root for the output of this refactor.
- `{caret_*}` - The file and position of the caret; can be either a point or a selection. The position is of format:
  - `line:column`, e.g. `8:13`
  - `line:column-line:column`, exclusive, e.g. `7:13-8:12`
- `{output_mode}`: either `file` or `stdout`. Default `file`, which dumps to the directory; choose `stdout` for debugging.
- `{check_mode}`: either `deferred` or `eager`. Default `deferred`, which does syntax check (or even type check in the future, when type checker is ready); choose `eager` if you want the user input to be strict and complete.
- `{refactor_candidate_file}`: a file containing the refactor candidates that the user inputs.

Note that

1. All paths can be relative.
2. `line` and `column` are 1-indexed numbers.
3. `{dump}` can be omitted if `{output_mode}` is `{stdout}`.
4. `{output_mode}` and `{check_mode}` can be omitted.

## Tests

Tests are rested in `Tests/editor`. An overview can be done by `tree`:

```
.
└── basic
│  ├── if
│  │  ├── arg
│  │  ├── in
│  │  └── proj
│  │     └── t.arm
│  ├── ifcond
│  │  ├── arg
│  │  ├── in
│  │  └── proj
│  │     └── t.arm
│  ....
....
```

Tests are divided by classes `basic`, `range` and `error`, under each lies all the tests. A test is comprised of `arg`, `in` and directories of `proj` and `expect`. The `proj` contains a short Starmada project as a real user project, and the `expect` is the expected output of it. The `error` tests can only be tested by hand, because we currently lack the means to detect a runtime error. If a clean way to do this in Python is known, we can add them to the test suit in no time. 

## Core Concepts

Before diving into detailed code documentation, there are several concepts (or data structures) that we should first investigate. Some of them can be composed together and form a new type.

### Chain

A chain, often represented by a `List`, is a totally ordered set. It requires an index (`Idx`) to destruct. In Starmada both levels and proofs are chains.

### Summary

`Summary`s hold data in a structured manner. There are three types of `Summary`s: `ProjectSummary`, `LevelSummary` and `ProofSummary`, each holding a level of abstraction. `LevelSummary` is managed by a chain, which is a `List` containing all levels in order.

### Sequence (`Seq`)

A sequence is an abstract `List` designed for Myers Diff Algorithm.

### Location (`Loc`)

Location presents the position of a statement in a certain method of a certain level. `StmtLoc`, for example, contains a level name, a method name, and an index of the statement in the corresponding `StatementSeq`.

### Token

Token presents a piece of consecutive source code text. It's comprised of a beginning position and an ending position. The name token is taken because the content is unseparable.

### Group

A group is a list of content that have the potential to be grouped as a whole. It may or may not end up in a cluster, but it can always be iterated.

## Code Documentation

With the comments written in the source code and a few core concepts explained above, this is only an outline of dataflow.

### Driver

The `Driver` is responsible for parsing the input files and deciding the order of the levels using proofs. It outputs `ProjectSummary`, which contains most of the information for the refactor. It also generates `LevelInfo` that maps levels' name to the file it lives and the index in the chain.

### Mapper

The `Mapper` builds a level-wise mapping from the lowest level in propagation to the highest by calling the function `IdentifyByStatementSelection`. It also picks the right equivalence between statements using function `EqualityPicker`. Deep inside, it uses `Diff`, which implements the Myers Diff Algorithm.

### Diff

The implementation of the Myers Diff Algorithm. Uses `MapExactForward` and `MapExactBackward` to build up the map. Uses class `Route` to represent an editting path, and picks `key_route`, which is the shortest path of all editting paths.

### RefactorBuffer

After all the preparations, the `RefactorBuffer` actually performs the refactoring. It's done in a lazy fashion, where all the potential changes to the file is recorded in `Schema`, and are applied from the bottom of the file all the way up to the top to avoid messing up the position of the changes. The final dump is performed using class `RefactorProjectBuffer`.

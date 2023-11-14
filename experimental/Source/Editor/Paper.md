# Multi-level Editor for Starmada

## Introduction

The Starmada code involves multiple levels of codes that are associated by proofs. Given the small step nature of the Starmada code, levels are often similar to each other while the difference is where the corresponding proof needs to justify. Reasonable as it sounds, the current scheme requires a cross-level refactor when any change is to be applied to the same piece of logic of the similar code, leaving the programmers with a considerable amount of manual refactoring work.

To make lifes of our Starmada programmers easier, we introduce the *multi-level editor for Starmada.* Giving semantic analysis based on structured Starmada AST, our editor is capable of preserving the syntactic correctness, as well as the original intention of the programmer, while refactoring. To complete the refactoring task, the editor asks for the range of level propagation, the candidate statement(s) that needs to be editted. Behind the scene, the editor runs a pair-wise level diffing and gets a mapping of every statement from the level it shows up to the level it disappears inside the range. Then the editor classifies the pattern of the statements into either a) clustered: treat the statements as a whole and replace all with the given input code, or b) separated: treat the statement as a list of individuals and perform refactor on statement basis. The output would be either a successful refactor that dumps code with correct syntax (and optionally, type safe) or an error prompt.

## Motivation

To perform the refactoring, we need to identify pieces of "similar" code across all levels being propagated. A typical diff tool can do the job, but not necessarily in an ideal way. Consider the following lines of code for declaring a variable `x` of type `int` and instantiating it with value `1`:

```
int x := 1;
 int  x   :=1;
int x ::= 1;
```

The first two lines should be undoubtedly considered the same since they are syntactically the same statement, while the third line should under certain condition be treated as "similar", such as when it's right before an TSO elimination.

The traditional approaches fail to accept the programs that are syntactically identical but not identical character-by-character. Even if the whitespaces are removed, they fail to understand the program; there could be situation where the source code looks different yet results in the same AST. A better approach which is adopted in this project is to parse the program first and perform analysis on the AST of the source code.

## The Core Algorithm

The core algorithm is derived from the [Myers Diff Algorithm]([diff2.pdf (xmailserver.org)](http://www.xmailserver.org/diff2.pdf)), which is a famous diff algorithm that works on sequence, with a given equivalence difinition on the sequence elements. In short, the algorithm finds the shortest editing path between the two sequences. Consider two sequences A = (a~1~, ..., a~m~) and B = (b~1~, ..., b~n~). Each step in the path is either add a~i~, add b~j~, or add both a~i~ and b~j~ when they are equivalent.

Traditionally the Myers Diff Algorithm works on sequences of characters or lines to tell the difference between two given strings. While text-level diffing is commonly used in situations such as git diff, it's not ideal in our use case since we desire a syntax-directed refactor that produces better preservation the structure of the code and, as a result, better conjecture of programmer's intention.

To apply the algorithm, we have two pieces missing in our puzzle. First, the AST is a tree, but we need two sequences as input; and second, the equivalence relation of statements is not trivial. We'll given solutions in the following two paragraphs.

## AST Flattening

To apply the algorithm on Starmada AST, we choose to flatten the AST into a sequence by encoding hierarchy structures into delimiter-surrounded blocks. Each statement carries its position information in the source code, which relieves the burden for further locating before replacing them. Since there’s no need of recovering the original structural information (though we can), we consider the flattening as a one-way operation.

There are three types of block-shaped statement in Starmada: `atomic` block, `if` block and `while` block.  For the beginning and ending of each statement a corresponding delimiter statement is defined. A `flatten` function recursively replaces the block-shaped statements in a list of statements with the statements inside surrounded by the delimiter statements, and outputs a statement sequence where no block-shaped statement remains.

## Strategy as Heuristics

To establish the equivalence relation between statements, the strategy of the transition from the lower level to the higher level is utilized. There are three types of strategies that have syntax implication: variable introduction, variable hiding and TSO elimination.

For a pair of statements from the lower and upper level respectively, they should not be equal if the variable is introduced in the lower level or is hidden in the upper level, and they should be equal if the lower one is a TSO-bypassing assignment, given the corresponding strategy.

The rest of the strategies don't have a trivial explanation, i.e. the statements can't be considered equivalent only by its syntax. For now we consider the AST equivalence as a fallback option; in the future it may be possible to utilize the proof and find a better equivalence relation between statements for the other strategies taken.

## Candidate Statement Sanity Checker

After the selection of statements to be refactored and the level propagation range, the programmer inputs the replacement for the statements selected called the *candidate statements*. They should be well-formed Starmada statements with a correct syntax. To enforce this assumption, a sanity checker is provided which parses the candidate statements and test whether they are syntactically correct.

## Refactoring Selections

Using the method described, we can form a chain of equivalence relation between statements that links from the lowest level all the way up to the highest level. If the target is merely one statement, the refactoring is almost obvious: we can just find all statements on the chain that is considered identical to the one chosen and refactor them. However, if the target is a selection of multiple statements, the intention of the programmer becomes blurry. It could be the case that the programmer wants to treat the selected statements as a whole and replace them with together; or it could be the case that the programmer wants to see them as separate statements and change them one by one.

To satisfy both needs, a multi-statement refactoring adheres to the following procedure:

1. Go through all the levels on the chain and decide if the selection is clusterred in every level involved. Here *clusterred* means there's no other statement inserted in the selected statements in any level.
2. If the selection is clusterred, delete the statements on all levels involved and insert the replacement in the same place.
3. Otherwise, break the statements down to separate statements and do the ordinary refactor statement by statement. The number of candidate statements for replacement shoud match the statements selected, otherwise the refactoring would result in an error.

To avoid the undesirable refactoring result, the editor tend to fail fast instead of coming up with a solution that is not likely to be correct. If the transition is not absolutely clear and explicit, it's the programmer's responsibility to clarify the intention. It could be the case that the programmer needs multiple refactoring actions instead of just one multi-statement refactoring to disambiguate the transition.










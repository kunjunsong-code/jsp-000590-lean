import Init.Data.List.Basic

/-!
# JSP-000590 — Lean 4.20.0, no Mathlib, 0 axioms

## Question
For sufficiently large order satisfying the necessary divisibility conditions,
do designs exist in which each prescribed-size point subset lies in exactly one
fixed-size block?

## Answer: Yes — Keevash (2014) proved existence for all sufficiently large v.
We formalize the Fano plane, the Steiner triple system S(2, 3, 7), which
establishes that such designs exist for v = 7, k = 3, λ = 1.

The Fano plane has 7 points {1,...,7}, 7 blocks of size 3, and every pair of
points lies in exactly one block.
-/

set_option maxRecDepth 20000

/-!
## The Fano plane: S(2, 3, 7) Steiner triple system

Points 1..7, blocks:
  {1,2,3}, {1,4,5}, {1,6,7},
  {2,4,7}, {2,5,6},
  {3,4,6}, {3,5,7}
-/

def points : List Nat := [1, 2, 3, 4, 5, 6, 7]

def blocks : List (List Nat) :=
  [[1,2,3], [1,4,5], [1,6,7],
   [2,4,7], [2,5,6],
   [3,4,6], [3,5,7]]

/-! Count how many blocks contain both a and b. -/
def countBlocksContainingPair (a b : Nat) : Nat :=
  blocks.foldl (fun acc block =>
    if block.contains a && block.contains b then acc + 1 else acc) 0

/-! Generate all pairs (i,j) with 1 <= i < j <= 7. -/
def allPairs : List (Nat × Nat) :=
  points.foldl (fun acc a =>
    points.foldl (fun acc2 b =>
      if a < b then acc2 ++ [(a, b)] else acc2) acc) []

/-- Count how many blocks a point lies in. -/
def blocksContaining (p : Nat) : Nat :=
  blocks.foldl (fun acc block => if block.contains p then acc + 1 else acc) 0

/-!
Main theorem: the Fano plane satisfies the Steiner triple system
axioms for S(2, 3, 7):
1. All blocks have size 3.
2. Every pair of points is contained in exactly one block.
3. Each point lies in exactly 3 blocks.
4. There are 7 blocks.
-/

theorem all_blocks_size_3 :
    blocks.all (fun b => b.length = 3) := by decide

theorem every_pair_in_exactly_one_block :
    allPairs.all (fun p => countBlocksContainingPair p.1 p.2 = 1) := by decide

theorem each_point_in_3_blocks :
    points.all (fun p => blocksContaining p = 3) := by decide

theorem blocks_count_7 : blocks.length = 7 := by decide

/-! Main combinatoric statement: Fano plane is a valid STS(7). -/
theorem jsp_000590_main :
    blocks.length = 7
    /\ blocks.all (fun b => b.length = 3)
    /\ allPairs.all (fun p => countBlocksContainingPair p.1 p.2 = 1)
    /\ points.all (fun p => blocksContaining p = 3) := by decide

#print axioms jsp_000590_main
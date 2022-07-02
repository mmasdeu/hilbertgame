import .incidenceplane --hide
open IncidencePlane --hide
/- Tactic : intro

## Summary:

`intro p` will turn a goal `⊢ P → Q` into a hypothesis `p : P`
and goal `⊢ Q`. If `P` and `Q` are sets `intro p` means "let $p$ be an arbitrary element of $P$".
If `P` and `Q` are propositions then `intro p` says "assume $P$ is true". 

## Details

If your goal is a function or an implication `⊢ P → Q` then `intro`
will always make progress. `intro p` turns

`⊢ P → Q`

into 

```
p : P
⊢ Q
```

The opposite tactic to intro is `revert`; given the situation
just above, `revert p` turns the goal back into `⊢ P → Q`.

**Variant:** Instead of calling `intro` multiple times, you can use
`intros`. That is, `intros h₁ h₂` is equivalent to `intro h₁, intro h₂`.

## Example

If your goal is an implication $P\implies Q$ then Lean writes
this as `⊢ P → Q`, and `intro p,` can be thought of as meaning
"let $p$ be a proof of $P$", or more informally "let's assume that
$P$ is true". The goal changes to `⊢ Q` and the hypothesis `p : P`
appears in the local context.

-/


variables {Ω : Type} [IncidencePlane Ω] --hide

/- Lemma : no-side-bar
If two lines contain two distinct points, then they are the same
-/
lemma equal_lines_of_contain_two_points {A B : Ω}	{r s : Line Ω}
(hAB: A ≠ B)	(hAr: A ∈ r) (hAs: A ∈ s) (hBr: B ∈ r) (hBs: B ∈ s) :	r = s :=
begin
  rw incidence hAB hAr hBr,
  rw incidence hAB hAs hBs,


end




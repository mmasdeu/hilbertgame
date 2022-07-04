import .incidenceplane --hide
open IncidencePlane --hide

/- Tactic : left and right
## Summary
`left` and `right` work on the goal, and they change
`⊢ P ∨ Q` to `⊢ P` and `⊢ Q` respectively.
## Details
The tactics `left` and `right` work on a goal which is a type with
two constructors, the classic example being `P ∨ Q`. 
To prove `P ∨ Q` it suffices to either prove `P` or prove `Q`,
and once you know which one you are going for you can change
the goal with `left` or `right` to the appropriate choice.
-/


import incidence_world.level02 --hide
open IncidencePlane --hide

/-
In order to prove the next theorem, we will need to prove this lemma that 
will help us to deduce that the two points are different.
-/

variables {Ω : Type} [IncidencePlane Ω] --hide

/- Lemma : no-side-bar
If a point `P` is in a line and a point `Q` is not, then they are different.
-/
lemma point_in_line_not_point {P Q: Ω} {r : Line Ω} (hP : P ∈ r) (hQ : Q ∉ r): P ≠ Q :=
begin
  intro H,
  rw H at hP,
  exact hQ hP,
  
  
  
  
end

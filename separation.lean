import basic
open IncidencePlane

noncomputable theory
open_locale classical

variables {Ω : Type} [IncidencePlane Ω]
variables {A B C P Q R : Ω}
variables {ℓ r s t : Line Ω}

lemma same_side_trans_of_noncollinear (h : ¬ collinear ({A, C, B} : set Ω)):
    same_side ℓ A B → same_side ℓ B C → same_side ℓ A C :=
begin
  sorry
end

-- our lemma :D
lemma collinear_iff_on_line_through (X Y Z : Ω ) (h: X ≠ Y) : (collinear({X, Y, Z} : set Ω )) ↔  Z ∈ line_through X Y :=
begin
sorry,
end

-- our other lemma
lemma not_same_line_different_points (X Y :  Ω) (h : X ≠ Y) : (line_through({X, Y}))
begin
sorry,
end
-- added
lemma line_through_from_and (P Q : Ω) (ℓ : Line Ω) (h1 : P ≠ Q)
(h2 : P ∈ ℓ ∧ Q ∈ ℓ) : ℓ = line_through P Q :=
begin
cases h2 with hP hQ,
exact incidence h1 hP hQ,
end

-- added
lemma point_in_line_not_point {P Q: Ω} {r : Line Ω} (hP : P ∈ r) (hQ : Q ∉ r): P ≠ Q :=
begin
  intro h1,
  apply hQ,
  rw ← h1,
  exact hP,
end

lemma exists_point_not_in_line (ℓ : Line Ω) : ∃ (P : Ω), P ∉ ℓ :=
begin
rcases (existence Ω) with ⟨A : Ω, B, C, ⟨h1, h2, h3, h4⟩⟩,
by_cases h: line_through A B = ℓ,
{ use C,
  rw ← h,
  exact h4 },
{ by_cases a: A ∈ ℓ, { use B,
    intro p,
    apply h,
    rw incidence h1 a p },
  { use A }, },
end

lemma auxiliary_point (ℓ : Line Ω) (h : collinear ({A, B, C} : set Ω)) (hA : A ∉ ℓ) (hB : B ∉ ℓ)
  (hC : C ∉ ℓ) (hAB : A ≠ B) (hAC : A ≠ C) (hBC : B ≠ C)  :
  ∃ (D E : Ω), D ∈ ℓ ∧ ¬ E ∈ ℓ ∧ same_side ℓ A E ∧ (D * A * E) ∧
  ¬ collinear ({A, B, E} : set Ω) ∧
  ¬ collinear ({E, C, B} : set Ω) ∧
  ¬ collinear ({A, C, E} : set Ω)  :=
begin
    -- define what a b c line is, m
    set m := line_through A B with hm,
    
    have hAM: A ∈ m,
    exact line_through_left A B,

    have hBM: B ∈ m,
    exact line_through_right A B,

    have hCM:= (collinear_iff_on_line_through A B C hAB).1 h,
    
    --rcases (line_contains_two_points ℓ) with ⟨D1, D2, hD1,l⟩, 
--    cases h with h h2,

    --l is not m
    
    by_cases fdg: D1 ∈ m,
    {
      use D1,
    },
    {
      sorry
    },
    
    --there is point in l, not in m, D

    --D*A*E w point on ray

    -- D A E are collinear collinear of between, meaning there is a line s. Have to get a line

    -- l is different s

    -- E is not in l.

    -- A E same side of l

    -- E is not in m.
    -- 
    


--  rcases (exists_point_on_line ℓ) with ⟨F, hF⟩,
  --have g:= point_in_line_not_point hE hD,

end

lemma same_side_trans_of_collinear (h : collinear ({A, C, B} : set Ω)):
    same_side ℓ A B → same_side ℓ B C → same_side ℓ A C :=
begin
  sorry
end

lemma same_side_trans_general : same_side ℓ A B → same_side ℓ B C → same_side ℓ A C :=
begin
  sorry
end

lemma at_least_two_classes (ℓ : Line Ω):
      ∃ A B : Ω, (A ∉ ℓ) ∧ (B ∉ ℓ) ∧ (¬ same_side ℓ A B) :=
begin
  sorry
end

lemma at_most_two_classes_of_noncollinear (hA : A ∉ ℓ) (hB : B ∉ ℓ) (hC : C ∉ ℓ)
    (hBneqC : B ≠ C) (hAB: ¬ same_side ℓ A B) (hAC: ¬ same_side ℓ A C)
    (h : ¬ collinear ({A, B, C} : set Ω)) : same_side ℓ B C :=
begin
  sorry
end

lemma at_most_two_classes_of_collinear (hA : A ∉ ℓ) (hB : B ∉ ℓ) (hC : C ∉ ℓ)
    (hBneqC : B ≠ C) (hAB: ¬ same_side ℓ A B) (hAC: ¬ same_side ℓ A C)
    (h : collinear ({A, B, C} : set Ω)) : same_side ℓ B C :=
begin
  sorry
end

lemma at_most_two_classes_general (hA : A ∉ ℓ) (hB : B ∉ ℓ) (hC : C ∉ ℓ)
    (hBneqC : B ≠ C) (hAB: ¬ same_side ℓ A B) (hAC: ¬ same_side ℓ A C): same_side ℓ B C :=
begin
  sorry
end

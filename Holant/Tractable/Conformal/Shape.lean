import Holant.Tractable.Conformal.Completion

/-! One shared diagonal/antidiagonal shape, with exact layer and support transport. -/
namespace Holant.Tractable
noncomputable section
namespace Conformal

def HasShape (D : InvertibleKernel) (opposite : Bool) (s t : AlgebraicComplex) : Prop :=
  D.matrix = if opposite then Kernel.mul (diagonalKernel s t) Signature.disequality
    else diagonalKernel s t

theorem hasShape_of_xConformal {D : InvertibleKernel} (hD : XConformal D) :
    ∃ opposite : Bool, ∃ s t : AlgebraicComplex, s ≠ 0 ∧ t ≠ 0 ∧ HasShape D opposite s t := by
  obtain ⟨s, t, hs, ht, h | h⟩ := hD.diagonal_or_antidiagonal
  · exact ⟨false, s, t, hs, ht, h⟩
  · exact ⟨true, s, t, hs, ht, h⟩

theorem shape_action {D : InvertibleKernel} {opposite : Bool} {s t : AlgebraicComplex}
    (hD : HasShape D opposite s t) {n : ℕ} (f : Signature AlgebraicComplex n) :
    D.action f = fun x => diagonalCoefficient s t x * f (flipWord opposite x) := by
  unfold InvertibleKernel.action
  rw [hD]
  cases opposite
  · exact coordinateAction_diagonal s t f
  · exact coordinateAction_antidiagonal s t f

theorem shape_support {D : InvertibleKernel} {opposite : Bool} {s t : AlgebraicComplex}
    (hD : HasShape D opposite s t) (hs : s ≠ 0) (ht : t ≠ 0)
    {n : ℕ} (f : Signature AlgebraicComplex n) (x : Fin n → Bool) :
    D.action f x ≠ 0 ↔ f (flipWord opposite x) ≠ 0 := by
  rw [shape_action hD]
  exact mul_ne_zero_iff.trans (and_iff_right (diagonalCoefficient_ne_zero hs ht x))

theorem flipLayer_twice (opposite : Bool) {n d : ℕ} (hd : d ≤ n) :
    flipLayer opposite n (flipLayer opposite n d) = d := by
  cases opposite <;> simp [flipLayer]; omega

theorem weight_flip_eq_iff {n d : ℕ} (hd : d ≤ n) (opposite : Bool)
    (x : Fin n → Bool) :
    Holant.weight (flipWord opposite x) = d ↔ Holant.weight x = flipLayer opposite n d := by
  cases opposite
  · rfl
  · have hw : Holant.weight (complementWord x) + Holant.weight x = n :=
      Holant.weight_compl_add x
    change Holant.weight (complementWord x) = d ↔ Holant.weight x = n - d
    omega

theorem shape_action_singleLayer {D : InvertibleKernel} {opposite : Bool}
    {s t : AlgebraicComplex} (hD : HasShape D opposite s t)
    {n d : ℕ} {f : Signature AlgebraicComplex n} (hf : Signature.SingleLayer f d)
    (hd : d ≤ n) :
    D.action f = fun x =>
      (s ^ (n - flipLayer opposite n d) * t ^ flipLayer opposite n d) *
        f (flipWord opposite x) := by
  rw [shape_action hD]
  funext x
  by_cases hx : Holant.weight x = flipLayer opposite n d
  · rw [diagonalCoefficient_eq_weight, hx]
  · have hfz : f (flipWord opposite x) = 0 :=
      hf _ (fun he => hx ((weight_flip_eq_iff hd opposite x).mp he))
    simp only [hfz, mul_zero]

theorem shape_singleLayer {D : InvertibleKernel} {opposite : Bool}
    {s t : AlgebraicComplex} (hD : HasShape D opposite s t)
    {n d : ℕ} {f : Signature AlgebraicComplex n} (hf : Signature.SingleLayer f d)
    (hd : d ≤ n) : Signature.SingleLayer (D.action f) (flipLayer opposite n d) := by
  rw [shape_action_singleLayer hD hf hd]
  exact singleLayer_flip hf opposite hd _

theorem central_flip_iff {n : ℕ} (opposite : Bool) (x : Fin n → Bool) :
    2 * Holant.weight (flipWord opposite x) = n ↔ 2 * Holant.weight x = n := by
  cases opposite
  · rfl
  · have hw : Holant.weight (complementWord x) + Holant.weight x = n :=
      Holant.weight_compl_add x
    change 2 * Holant.weight (complementWord x) = n ↔ 2 * Holant.weight x = n
    omega

/-- Central restriction commutes with a conformal shape up to its exact
central-layer scalar and the same global complement choice. -/
theorem shape_centralRestriction {D : InvertibleKernel} {opposite : Bool}
    {s t : AlgebraicComplex} (hD : HasShape D opposite s t)
    {n : ℕ} (f : Signature AlgebraicComplex n) :
    Signature.centralRestriction (D.action f) = fun x =>
      (s ^ (n - n / 2) * t ^ (n / 2)) *
        Signature.centralRestriction f (flipWord opposite x) := by
  funext x
  rw [shape_action hD]
  by_cases hx : 2 * Holant.weight x = n
  · have hh := (central_flip_iff opposite x).mpr hx
    have hw : Holant.weight x = n / 2 := by omega
    simp only [Signature.centralRestriction, hx, hh, ↓reduceIte]
    rw [diagonalCoefficient_eq_weight, hw]
  · have hh := mt (central_flip_iff opposite x).mp hx
    simp [Signature.centralRestriction, hx, hh]

theorem shape_commonOneSided {D : InvertibleKernel} {opposite : Bool}
    {s t : AlgebraicComplex} (hD : HasShape D opposite s t) (hs : s ≠ 0) (ht : t ≠ 0)
    {G : SignatureFamily AlgebraicComplex} (hG : CommonOneSided G) :
    CommonOneSided (familyAction D G) := by
  cases opposite
  · rcases hG with hG | hG
    · left; rintro h ⟨g, hg, rfl⟩ x hx
      exact hG g hg x ((shape_support hD hs ht g.2 x).mp hx)
    · right; rintro h ⟨g, hg, rfl⟩ x hx
      exact hG g hg x ((shape_support hD hs ht g.2 x).mp hx)
  · rcases hG with hG | hG
    · right; rintro h ⟨g, hg, rfl⟩ x hx
      have hp := hG g hg (complementWord x) ((shape_support hD hs ht g.2 x).mp hx)
      have hc : Holant.charge (complementWord x) = -Holant.charge x := Holant.charge_compl x
      omega
    · left; rintro h ⟨g, hg, rfl⟩ x hx
      have hp := hG g hg (complementWord x) ((shape_support hD hs ht g.2 x).mp hx)
      have hc : Holant.charge (complementWord x) = -Holant.charge x := Holant.charge_compl x
      omega

theorem shape_bothChargeSigns {D : InvertibleKernel} {opposite : Bool}
    {s t : AlgebraicComplex} (hD : HasShape D opposite s t) (hs : s ≠ 0) (ht : t ≠ 0)
    {G : SignatureFamily AlgebraicComplex} (hG : BothChargeSigns G) :
    BothChargeSigns (familyAction D G) := by
  obtain ⟨⟨g, hg, x, hx, hn⟩, ⟨h, hh, y, hy, hp⟩⟩ := hG
  have hgnz : D.action g.2 (flipWord opposite x) ≠ 0 := by
    apply (shape_support hD hs ht _ _).mpr
    simpa only [flipWord_twice] using hx
  have hhnz : D.action h.2 (flipWord opposite y) ≠ 0 := by
    apply (shape_support hD hs ht _ _).mpr
    simpa only [flipWord_twice] using hy
  cases opposite
  · exact ⟨⟨_, ⟨g, hg, rfl⟩, x, hgnz, hn⟩, ⟨_, ⟨h, hh, rfl⟩, y, hhnz, hp⟩⟩
  · have hcx : Holant.charge (complementWord x) = -Holant.charge x := Holant.charge_compl x
    have hcy : Holant.charge (complementWord y) = -Holant.charge y := Holant.charge_compl y
    exact ⟨⟨_, ⟨h, hh, rfl⟩, complementWord y, hhnz, by omega⟩,
      ⟨_, ⟨g, hg, rfl⟩, complementWord x, hgnz, by omega⟩⟩

end Conformal
end
end Holant.Tractable

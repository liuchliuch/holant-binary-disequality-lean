import Holant.Dihedral.SixPortBase.Factor

/-! The P/P singleton branch exposes an exact unary factor on an original
physical port. Opposite parity and singleton positions determine that port. -/
noncomputable section
namespace Holant.Dihedral.SixPortBase
open Holant Holant.Marked Holant.Dihedral.CompatibleClosure Holant.Dihedral.SectorRuling
open Holant.Dihedral.CompatibleCoefficientLine
set_option backward.isDefEq.respectTransparency false

 theorem HasFactor.reindex {h : Signature Scalar 6} (hh : HasFactor h) (o : Equiv.Perm (Fin 6)) :
    HasFactor (Tensor.reindex o h) := by
  rcases hh with ⟨p,u,v,hu,hv,he⟩|⟨p,u,v,hu,hv,he⟩
  · exact Or.inl ⟨p.trans o,u,v,hu,hv,by rw [he,Tensor.reindex_trans]⟩
  · exact Or.inr ⟨p.trans o,u,v,hu,hv,by rw [he,Tensor.reindex_trans]⟩

 theorem factor_fixed_first (h : Signature Scalar 6) (hn : h ≠ 0) (b : Bool)
    (hz : ∀ x,x 0 ≠ b → h x=0) : HasFactor h := by
  let u : Signature Scalar 1 := fun x => if x 0=b then 1 else 0
  let v : Signature Scalar 5 := fun x => h (Fin.cons b x)
  let p : (Fin 1 ⊕ Fin 5) ≃ Fin 6 := Equiv.ofBijective (Sum.elim ![0] ![1,2,3,4,5]) (by decide)
  have he : h=Tensor.reindex p (Tensor.tensor u v) := by
    funext x
    have hp0 : p (.inl 0)=0 := rfl
    have hpr (i : Fin 5) : p (.inr i)=i.succ := by fin_cases i <;> rfl
    simp only [Tensor.reindex,Tensor.tensor,u,v,hp0,hpr]
    change h x=(if x 0=b then 1 else 0)*h (Fin.cons b (fun i => x i.succ))
    by_cases hb : x 0=b
    · rw [if_pos hb,one_mul]
      congr 1
      funext i
      refine Fin.cases ?_ (fun j => ?_) i
      · exact hb
      · rfl
    · rw [if_neg hb,zero_mul]
      exact hz x hb
  exact Or.inl ⟨p,u,v,(nonzero_factors p h u v hn he).1,(nonzero_factors p h u v hn he).2,he⟩

 theorem factor_fixed_second (h : Signature Scalar 6) (hn : h ≠ 0) (b : Bool)
    (hz : ∀ x,x 1 ≠ b → h x=0) : HasFactor h := by
  let o : Equiv.Perm (Fin 6) := Equiv.swap 0 1
  let q := Tensor.reindex o h
  have hq : q ≠ 0 := by
    intro he
    apply hn
    have hh := congrArg (Tensor.reindex o.symm) he
    have hz : Tensor.reindex o.symm (0 : Signature Scalar 6)=0 := rfl
    simpa only [q,Tensor.reindex_symm,hz] using hh
  have hfactor := factor_fixed_first q hq b (by
    intro x hx
    apply hz
    simpa [o] using hx)
  have hh := hfactor.reindex o.symm
  simpa [q] using hh

private theorem opposite_fixed : ∀ b₀ b₁ a b : Bool,b₀ ≠ b₁ →
    a=(if a ^^ b then b₁ else b₀) → b=b₀ := by decide

/-- Precisely one possible first bit in each opposite parity sector leaves
one of the two original distinguished ports fixed. -/
 theorem singleton_sectors_factor (h : Signature Scalar 6) (hn : h ≠ 0)
    (b₀ b₁ : Bool)
    (hz : ∀ γ z y,z ≠ (if γ then b₁ else b₀) → h (pair z (z ^^ γ) y)=0) : HasFactor h := by
  by_cases he : b₀=b₁
  · apply factor_fixed_first h hn b₀
    intro x hx
    let γ := x 0 ^^ x 1
    have hh := hz γ (x 0) (fun i => x i.succ.succ) (by simpa [←he] using hx)
    have hp : (x 0 ^^ γ)=x 1 := by simp [γ]
    simpa only [hp,pair_eta] using hh
  · apply factor_fixed_second h hn b₀
    intro x hx
    let γ := x 0 ^^ x 1
    have hne : x 0 ≠ (if γ then b₁ else b₀) := by
      intro heq
      have hh : x 1=b₀ := opposite_fixed b₀ b₁ (x 0) (x 1) he heq
      exact hx hh
    have hh := hz γ (x 0) (fun i => x i.succ.succ) hne
    have hp : (x 0 ^^ γ)=x 1 := by simp [γ]
    simpa only [hp,pair_eta] using hh

 theorem proportional_singletons_factor {m : ℕ} (h : Signature Scalar 6) (hn : h ≠ 0)
    (E : ProportionalSector m (sectorFirst (s:=2) h false) (sectorSecond (s:=2) h false))
    (O : ProportionalSector m (sectorFirst (s:=2) h true) (sectorSecond (s:=2) h true))
    (hE : E.first=0 ∨ E.second=0) (hO : O.first=0 ∨ O.second=0) : HasFactor h := by
  have choose_bit (a b : Scalar) (hh : a=0 ∨ b=0) :
      ∃ c : Bool,∀ z : Bool,z ≠ c → (if z then b else a)=0 := by
    rcases hh with ha|hb
    · exact ⟨true,by intro z hz; cases z <;> simp_all⟩
    · exact ⟨false,by intro z hz; cases z <;> simp_all⟩
  obtain ⟨b₀,hb₀⟩ := choose_bit E.first E.second hE
  obtain ⟨b₁,hb₁⟩ := choose_bit O.first O.second hO
  apply singleton_sectors_factor h hn b₀ b₁
  intro γ z y hz
  cases γ <;> cases z
  · have ha : E.first=0 := hb₀ false hz
    have hh := congrFun E.first_exact y
    simpa [sectorFirst,ha] using hh
  · have ha : E.second=0 := hb₀ true hz
    have hh := congrFun E.second_exact y
    simpa [sectorSecond,ha] using hh
  · have ha : O.first=0 := hb₁ false hz
    have hh := congrFun O.first_exact y
    simpa [sectorFirst,ha] using hh
  · have ha : O.second=0 := hb₁ true hz
    have hh := congrFun O.second_exact y
    simpa [sectorSecond,ha] using hh

end Holant.Dihedral.SixPortBase

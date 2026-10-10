import Holant.Proofs.Hardness.GeneralOddResidueCharge
import Holant.Proofs.Hardness.GeneralOddMinimalTerminal

/-! Two-sided support upgrades the minimal odd graph's one-direction residue
to divisibility of EVERY supported original charge. The missing direction is
proved using actual disjoint copies, followed by actual proper-gcd descent. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralOddResidueMinimal
open Holant Holant.Tractable
open Holant.LocalDrafts.Hardness.GeneralExtraction
open NamedContraction SupportDescent SupportCaps NativeCopies
open Holant.LocalDrafts.BinaryInterpolation.SingularExtraction
open GeneralOddUnaryOrdinary GeneralOddUnarySource GeneralOddResidueCharge
set_option backward.isDefEq.respectTransparency false

variable {s : ℕ} {a : ℕ→ℕ}
variable (G : (i : Fin s)→Signature AlgebraicComplex (a i.val))
variable (D : GeneralOddMinimalTerminal.Minimal G)

/-- The minimality obstruction holds for an arbitrary actual graph over the
original family, not only for a single original row. -/
theorem native_opposite_divisible (b : Bool)
    (hb : GeneralOddMinimalTerminal.endpoint G D (!b)≠0)
    {m : ℕ} (P : Network AlgebraicComplex m)
    (hPF : Uses P (kCoordinates (original G))) (hPX : Native P)
    (x : Fin m → Bool) (hx : P.denote x≠0)
    (q : ℕ) (hq : 0<q) (hcharge : balance b x=q) : D.arity∣q := by
  by_contra hdiv
  let H := toNative D.graph
  have hHF : Uses H (kCoordinates (original G)) :=
    toNative_uses (original G) _ D.uses
  have hHX : Native H := toNative_native _ D.ordinary
  have hy : H.denote (fun _=>!b)≠0 := by
    simpa [H,toNative_denote,GeneralOddMinimalTerminal.endpoint] using hb
  have hn : 0<D.arity := by obtain ⟨k,hk⟩ := D.odd; omega
  obtain ⟨hd,hdn,r,t,hr,hrn,htq,he,U,hUF,hUX,hUb,hUv,hUe⟩ :=
    GeneralOddHighTerminalGcd.native_reduction (kCoordinates (original G))
      (by norm_num) b P H hPF hPX hHF hHX x hx hy q hq hcharge hn hdiv
  have hod : Odd (Nat.gcd q D.arity) :=
    Odd.of_dvd_nat D.odd (Nat.gcd_dvd_right _ _)
  have hdiag : sourceKBasis.symm.action (toOrdinary U).denote=U.denote := by
    rw [toOrdinary_denote,InvertibleKernel.symm_action_action]
  have hUnz : (toOrdinary U).denote≠0 := by
    intro hz
    have hh := congrArg sourceKBasis.symm.action hz
    rw [hdiag] at hh
    exact hUb (congrFun (hh.trans (Signature.coordinateAction_zero _)) (fun _=>b))
  have hmin := D.minimal (Nat.gcd q D.arity)
    ⟨hod,toOrdinary U,toOrdinary_uses (original G) U hUF,
      toOrdinary_ordinary U hUX,hUnz⟩
  omega

/-- Failure of the common-side predicate supplies an original positive
reservoir in either requested orientation. -/
theorem positive_original (hside : ¬CommonOneSided (kCoordinates (original G))) (b : Bool) :
    ∃ k : Fin s,∃ x : Fin (a k.val)→Bool,
      sourceKBasis.symm.action (G k) x≠0 ∧ 0<balance b x := by
  have hboth := (commonOneSided_or_bothChargeSigns (kCoordinates (original G))).resolve_left hside
  obtain ⟨g,hg,x,hx,hpos⟩ : ∃g∈kCoordinates (original G),
      ∃x,g.2 x≠0 ∧ 0<balance b x := by
    cases b
    · obtain ⟨g,hg,x,hx,hneg⟩ := hboth.1
      exact ⟨g,hg,x,hx,by rw [balance_false]; omega⟩
    · obtain ⟨g,hg,x,hx,hpos⟩ := hboth.2
      exact ⟨g,hg,x,hx,by rwa [balance_true]⟩
  obtain ⟨f,⟨k,rfl⟩,rfl⟩ := hg
  exact ⟨k,x,hx,hpos⟩

/-- The arity of a minimal nonzero odd graph divides both positive and
negative supported charges of every original row. -/
theorem all_balance_divisible (hh : 3≤D.arity)
    (hside : ¬CommonOneSided (kCoordinates (original G)))
    (k : Fin s) (x : Fin (a k.val)→Bool)
    (hx : sourceKBasis.symm.action (G k) x≠0) :
    (D.arity : ℤ)∣balance true x := by
  obtain ⟨b,hb⟩ := GeneralOddMinimalTerminal.supported_endpoint G D hh
  have hbal : (D.arity : ℤ)∣balance b x := by
    by_cases hnonneg : 0≤balance b x
    · by_cases hz : balance b x=0
      · rw [hz]; exact dvd_zero _
      · let q := (balance b x).toNat
        have hq : (q : ℤ)=balance b x := Int.toNat_of_nonneg hnonneg
        have hd := GeneralOddMinimalTerminal.opposite_divisible G D b hb k x q hx
          (by omega) hq.symm
        rw [←hq]
        exact_mod_cast hd
    · obtain ⟨j,y,hy,hypos⟩ := positive_original G hside b
      let q := (balance b y).toNat
      let r := (-balance b x).toNat
      have hq : (q : ℤ)=balance b y := Int.toNat_of_nonneg (le_of_lt hypos)
      have hr : (r : ℤ)=-balance b x := Int.toNat_of_nonneg (by omega)
      have hdq : D.arity∣q := GeneralOddMinimalTerminal.opposite_divisible G D b hb
        j y q hy (by omega) hq.symm
      let P := toNative (Network.corolla (G j))
      let Q := toNative (Network.corolla (G k))
      have hPF : Uses P (kCoordinates (original G)) :=
        toNative_uses (original G) _ (fun _=>⟨j,rfl⟩)
      have hQF : Uses Q (kCoordinates (original G)) :=
        toNative_uses (original G) _ (fun _=>⟨k,rfl⟩)
      obtain ⟨t,ht,hshift,N,hNF,hNX,w,hw,hcharge,hNv,hNe⟩ :=
        positive_shift (kCoordinates (original G)) b P Q hPF
          (toNative_native _ (fun e=>Fin.elim0 e)) hQF
          (toNative_native _ (fun e=>Fin.elim0 e)) y x
          (by simpa [P,toNative_denote] using hy)
          (by simpa [Q,toNative_denote] using hx)
          q r (by omega) hq.symm (by omega)
      have hdt := native_opposite_divisible G D b hb N hNF hNX w hw t ht hcharge
      have hdr := negative_dvd_of_shift hdq hdt hshift
      have hdr' : (D.arity : ℤ)∣(r : ℤ) := by exact_mod_cast hdr
      rw [hr] at hdr'
      exact dvd_neg.mp hdr'
  cases b
  · rw [balance_false] at hbal
    rw [balance_true]
    exact dvd_neg.mp hbal
  · exact hbal

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralOddResidueMinimal

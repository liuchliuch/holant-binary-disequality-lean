import Holant.Certificates.TetrahedralOrientation.Data

/-! Full finite expansions from the literal Frobenius ancestor through actual
I contraction and all four printed port matrices. Raw scalars are retained. -/
namespace Holant.Certificates.TetrahedralOrientation
open Holant Holant.Certificates.MatchingProductBridge
noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000
set_option backward.isDefEq.respectTransparency false

/-- The source's normalized rows, multiplied by their exact physical coefficients. -/
theorem dressed_exact (s : Orientation) : dressed s = rawScale s • terminal s := by
  fin_cases s <;> funext x <;>
    rcases h0 : x 0 with _ | _ <;> rcases h1 : x 1 with _ | _ <;>
    rcases h2 : x 2 with _ | _ <;> rcases h3 : x 3 with _ | _ <;>
    norm_num [dressed,Signature.coordinateAction,sum_four,Fintype.sum_bool,Fin.prod_univ_succ,
      card_apply,ancestor,Fin.sum_univ_succ,dual,cardImages,sigma,axisR,C,P2,
      Q0,Q1,Q2,Q3,Signature.equality,legs,Gplus,Gminus,terminal,evenTable,rawScale,
      h0,h1,h2,h3,smul_eq_mul] <;>
    ring_nf <;> norm_num [Complex.I_sq] <;> ring

theorem rawScale_ne_zero (s : Orientation) : rawScale s ≠ 0 := by
  fin_cases s <;> norm_num [rawScale,Complex.ext_iff]

/-- Every omitted odd entry vanishes in the actual dressed tensor. -/
theorem dressed_odd_zero (s : Orientation) (x : Fin 4 → Bool)
    (h : (x 0 ^^ x 1 ^^ x 2 ^^ x 3) = true) : dressed s x = 0 := by
  rw [dressed_exact]
  change rawScale s * terminal s x = 0
  have ht : terminal s x = 0 := by
    rcases h0 : x 0 with _ | _ <;> rcases h1 : x 1 with _ | _ <;>
      rcases h2 : x 2 with _ | _ <;> rcases h3 : x 3 with _ | _ <;>
      simp [h0,h1,h2,h3] at h <;> simp [terminal,h0,h1,h2,h3]
  rw [ht,mul_zero]

theorem dressed_zero_endpoint (s : Orientation) : dressed s (fun _ => false) = rawScale s := by
  rw [dressed_exact]
  fin_cases s <;> simp [terminal,evenTable,smul_eq_mul]

theorem dressed_one_endpoint (s : Orientation) : dressed s (fun _ => true) ≠ 0 := by
  rw [dressed_exact]
  change rawScale s * terminal s (fun _ => true) ≠ 0
  apply mul_ne_zero (rawScale_ne_zero s)
  fin_cases s <;> simp [terminal,evenTable,Complex.I_ne_zero]

theorem dressed_endpoints_nonzero (s : Orientation) :
    dressed s (fun _ => false) ≠ 0 ∧ dressed s (fun _ => true) ≠ 0 := by
  exact ⟨by rw [dressed_zero_endpoint]; exact rawScale_ne_zero s,dressed_one_endpoint s⟩

end
end Holant.Certificates.TetrahedralOrientation

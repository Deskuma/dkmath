import Mathlib
import P2M.Util
import P2M.Sol.S_flt_regular

open scoped NumberField
theorem flt_regular {p : ℕ} [Fact p.Prime] (hreg : p.Coprime (Fintype.card (ClassGroup (𝓞 (CyclotomicField p ℚ))))) (hodd : p ≠ 2) : FermatLastTheoremFor p := by p2m_exact_reverting @_root_.P2MW.S_flt_regular.solution

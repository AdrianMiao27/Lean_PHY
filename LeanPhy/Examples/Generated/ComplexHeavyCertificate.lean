import LeanPhy.Mathematics.MatrixCertificate

/- Generated exact data. Python output is untrusted until Lean checks `accepted`.
   Input digest: fea367236e5cb0f1a0246a72a53d5e2d45d185a08e351a2004cb30cd3a977962. -/
namespace LeanPhy.Generated.MatrixCertificates.ComplexHeavy

open LeanPhy.Mathematics LeanPhy.Mathematics.MatrixCertificate

def nominal : RationalMatrix 2 2 :=
  ⟨!![(4 / 1 : ℚ), (0 / 1 : ℚ); (0 / 1 : ℚ), (4 / 1 : ℚ)], !![(0 / 1 : ℚ), (1 / 1 : ℚ); (-1 / 1 : ℚ), (0 / 1 : ℚ)]⟩

def candidate : Candidate 2 where
  inverse := ⟨!![(1 / 4 : ℚ), (0 / 1 : ℚ); (0 / 1 : ℚ), (1 / 4 : ℚ)], !![(0 / 1 : ℚ), (0 / 1 : ℚ); (0 / 1 : ℚ), (0 / 1 : ℚ)]⟩
  inverseBound := (1 / 4 : ℚ)
  residualBound := (1 / 4 : ℚ)
  modelRadius := (1 / 1 : ℚ)

-- `decide` is reduced by the Lean kernel; no native decision axiom is used.
theorem accepted : candidate.Accepted nominal := by decide +kernel

theorem valid : Valid nominal candidate := sound nominal candidate accepted

def envelope : CertificateEnvelope (Candidate 2) where
  metadata :=
    { producer := "matrix_certificate.py"
      format := "complex-rational-matrix-v1"
      digest := "fea367236e5cb0f1a0246a72a53d5e2d45d185a08e351a2004cb30cd3a977962"
      source := "exact matrix data with declared norm-ball radius" }
  payload := candidate

def certificate : VerifiedCertificate (checker nominal candidate) :=
  verifyEnvelope (checker nominal candidate) envelope (by
    change candidate = candidate ∧ candidate.Accepted nominal
    exact ⟨rfl, accepted⟩)

end LeanPhy.Generated.MatrixCertificates.ComplexHeavy

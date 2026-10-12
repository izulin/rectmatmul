module

public import OAI.LinearAlgebra.MatrixMultiplication.AllFieldsAudit

public section

/-!
# Verified upstream baseline

This module builds the existing all-fields theorem and its guarded axiom
audit from the preserved Palomar snapshot. It contains no new rectangular
matrix multiplication result.
-/

#check OAI.MatrixMultiplication.omega_le_nine_quarters
#check OAI.MatrixMultiplication.AuxiliarySeparation.matrix_multiplication_cost_le

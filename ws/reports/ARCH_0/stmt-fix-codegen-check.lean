noncomputable section
namespace CodegenCheck
private def leaf : Nat := 0xff
def root : Nat := leaf + 1
noncomputable def explicit : Nat := leaf + 2
end CodegenCheck

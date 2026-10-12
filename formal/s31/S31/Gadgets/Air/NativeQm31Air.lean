import S31.Gadgets.Air.Qm31Ops

/-! Generated from the native qm31_ops constraint trees. Do not edit. -/
namespace S31.Gadgets.Air.NativeQm31Air
open S31.Gadgets.Packed
open S31.Gadgets.Air.Qm31Ops

def residuals (f : Flags) (x y output : Quad) : List F := [
  ((((f.add + f.sub) + f.mul) + f.pointwiseMul) - (1 : F)),
  (f.add * (f.add - (1 : F))),
  (f.sub * (f.sub - (1 : F))),
  (f.mul * (f.mul - (1 : F))),
  (f.pointwiseMul * (f.pointwiseMul - (1 : F))),
  (output.a - (((((((((x.a * y.a) - (x.b * y.b)) + ((2 : F) * ((x.c * y.c) - (x.d * y.d)))) - (x.c * y.d)) - (x.d * y.c)) * f.mul) + ((x.a + y.a) * f.add)) + ((x.a - y.a) * f.sub)) + ((x.a * y.a) * f.pointwiseMul))),
  (output.b - (((((((((x.a * y.b) + (x.b * y.a)) + ((2 : F) * ((x.c * y.d) + (x.d * y.c)))) + (x.c * y.c)) - (x.d * y.d)) * f.mul) + ((x.b + y.b) * f.add)) + ((x.b - y.b) * f.sub)) + ((x.b * y.b) * f.pointwiseMul))),
  (output.c - ((((((((x.a * y.c) - (x.b * y.d)) + (x.c * y.a)) - (x.d * y.b)) * f.mul) + ((x.c + y.c) * f.add)) + ((x.c - y.c) * f.sub)) + ((x.c * y.c) * f.pointwiseMul))),
  (output.d - ((((((((x.a * y.d) + (x.b * y.c)) + (x.c * y.b)) + (x.d * y.a)) * f.mul) + ((x.d + y.d) * f.add)) + ((x.d - y.d) * f.sub)) + ((x.d * y.d) * f.pointwiseMul)))
]

end S31.Gadgets.Air.NativeQm31Air

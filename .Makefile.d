src/BaseSystem.vo src/BaseSystem.glob src/BaseSystem.v.beautified src/BaseSystem.required_vo: src/BaseSystem.v src/Smallstep.vo src/Maps.vo
src/BaseSystem.vio: src/BaseSystem.v src/Smallstep.vio src/Maps.vio
src/BaseSystem.vos src/BaseSystem.vok src/BaseSystem.required_vos: src/BaseSystem.v src/Smallstep.vos src/Maps.vos
src/Imp.vo src/Imp.glob src/Imp.v.beautified src/Imp.required_vo: src/Imp.v src/Maps.vo
src/Imp.vio: src/Imp.v src/Maps.vio
src/Imp.vos src/Imp.vok src/Imp.required_vos: src/Imp.v src/Maps.vos
src/Maps.vo src/Maps.glob src/Maps.v.beautified src/Maps.required_vo: src/Maps.v 
src/Maps.vio: src/Maps.v 
src/Maps.vos src/Maps.vok src/Maps.required_vos: src/Maps.v 
src/OldSystem.vo src/OldSystem.glob src/OldSystem.v.beautified src/OldSystem.required_vo: src/OldSystem.v src/Smallstep.vo src/Maps.vo
src/OldSystem.vio: src/OldSystem.v src/Smallstep.vio src/Maps.vio
src/OldSystem.vos src/OldSystem.vok src/OldSystem.required_vos: src/OldSystem.v src/Smallstep.vos src/Maps.vos
src/Smallstep.vo src/Smallstep.glob src/Smallstep.v.beautified src/Smallstep.required_vo: src/Smallstep.v src/Maps.vo src/Imp.vo
src/Smallstep.vio: src/Smallstep.v src/Maps.vio src/Imp.vio
src/Smallstep.vos src/Smallstep.vok src/Smallstep.required_vos: src/Smallstep.v src/Maps.vos src/Imp.vos
src/Stlc.vo src/Stlc.glob src/Stlc.v.beautified src/Stlc.required_vo: src/Stlc.v src/Maps.vo src/Smallstep.vo
src/Stlc.vio: src/Stlc.v src/Maps.vio src/Smallstep.vio
src/Stlc.vos src/Stlc.vok src/Stlc.required_vos: src/Stlc.v src/Maps.vos src/Smallstep.vos
src/TypeSafety.vo src/TypeSafety.glob src/TypeSafety.v.beautified src/TypeSafety.required_vo: src/TypeSafety.v src/Smallstep.vo src/Maps.vo src/BaseSystem.vo
src/TypeSafety.vio: src/TypeSafety.v src/Smallstep.vio src/Maps.vio src/BaseSystem.vio
src/TypeSafety.vos src/TypeSafety.vok src/TypeSafety.required_vos: src/TypeSafety.v src/Smallstep.vos src/Maps.vos src/BaseSystem.vos

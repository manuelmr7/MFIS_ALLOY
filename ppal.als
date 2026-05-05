open util/boolean
-- 1. ENUMERACIONES (Traducido de OCL enum)

abstract sig EstadoVehiculo {}
one sig Operativo, Mantenimiento extends EstadoVehiculo {}

abstract sig ModoConduccion {}
one sig Autonomo, Manual extends ModoConduccion {}

abstract sig TipoZona {}
one sig Peatonal, Carga, Emergencia, Estandar extends TipoZona {}

abstract sig TipoPasajero {}
one sig EstandarPasajero, Oro extends TipoPasajero {}

abstract sig EstadoSensor {}
one sig OperativoSensor, Fallo extends EstadoSensor {}

-- 2. CLASES Y ASOCIACIONES (Traducido de OCL classes y associations)

sig CentroControl {
	estadoAlerta: one Bool,
	zonas: set Zona -- Asociación ZonaCentro (Inversa)
}

sig Zona {
	tipo: one TipoZona,
	capacidadMax: one Int
}

sig Sensor {
	esCritico: one Bool,
	estado: one EstadoSensor
}

sig Pasajero {
	edad: one Int,
	tipo: one TipoPasajero,
	tieneEquipajePesado: one Bool
}

sig Ruta {
	esPrioritaria: one Bool,
	tiempoEspera: one Int
}

sig vAutonomo {
	estado: one EstadoVehiculo,
	modo: one ModoConduccion,
	nivelBateria: one Int,
	numAsientos: one Int,
	velocidad: one Int,
	cierreSeguridad: one Bool,
	maleteroDisponible: one Bool,

-- Asociaciones directas
	sensores: set Sensor,
	pasajeros: set Pasajero,
	zona: one Zona,
	ruta: lone Ruta
}
-- 3. RESTRICCIONES (Traducido de OCL constraints)
fact ReglasDelSistema {

 -- 1. Cierre de seguridad niños < 12
	all v: vAutonomo | 
	(some p: v.pasajeros | p.edad < 12) implies v.cierreSeguridad = True

-- 2. Sensores críticos en modo autónomo
	all v: vAutonomo | 
	v.modo = Autonomo implies 
	(all s: v.sensores | s.esCritico = True implies s.estado = OperativoSensor)

-- 4. No arrancar si hay más pasajeros que asientos (adaptado a conteo)
	all v: vAutonomo | 
	v.velocidad > 0 implies #v.pasajeros <= v.numAsientos

-- 5. Capacidad máxima de zona
	all z: Zona | 
	#{v: vAutonomo | v.zona = z} <= z.capacidadMax

-- 6. Espera máxima 30 min en Rutas
	all r: Ruta | 
	r.tiempoEspera <= 30

-- 7. Equipaje pesado requiere maletero
	all v: vAutonomo | 
	(some p: v.pasajeros | p.tieneEquipajePesado = True) implies v.maleteroDisponible = True

-- 8. Velocidad en zona peatones <= 20
	all v: vAutonomo | 
	v.zona.tipo = Peatonal implies v.velocidad <= 20

-- 9. Batería < 10%
	all v: vAutonomo | 
	v.nivelBateria < 10 implies (no v.pasajeros and v.zona.tipo = Carga)

-- 11. Emergencia activa modo manual
	all v: vAutonomo | 
	v.zona.tipo = Emergencia implies v.modo = Manual

-- 12. Rutas prioritarias solo autónomos
	all r: Ruta | 
	r.esPrioritaria = True implies (all v: vAutonomo | v.ruta = r implies v.modo = Autonomo)

-- 13. Mantenimiento sin pasajeros (Regla creativa)
	all v: vAutonomo | 
	v.estado = Mantenimiento implies no v.pasajeros

-- 15. Carga parado
	all v: vAutonomo | 
	v.zona.tipo = Carga implies v.velocidad = 0
}

-- 4. OPERACIONES (Traducido de OCL pre/post conditions)
pred embarcarPasajero [v, v2: vAutonomo, p: Pasajero] {

-- Precondiciones
	#v.pasajeros < v.numAsientos
	v.nivelBateria >= 10
	p not in v.pasajeros

-- Postcondiciones (El nuevo estado v2 incluye a p)
	v2.pasajeros = v.pasajeros + p

-- Frame conditions (Mantenemos TODO el resto igual)
	v2.estado = v.estado
	v2.modo = v.modo
	v2.nivelBateria = v.nivelBateria
	v2.numAsientos = v.numAsientos
	v2.velocidad = v.velocidad
	v2.cierreSeguridad = v.cierreSeguridad
	v2.maleteroDisponible = v.maleteroDisponible
	v2.sensores = v.sensores
	v2.zona = v.zona
	v2.ruta = v.ruta
}

pred arrancar [v, v2: vAutonomo] {
-- Precondiciones
	#v.pasajeros <= v.numAsientos
	v.estado = Operativo
	v.velocidad = 0

-- Postcondiciones
	v2.velocidad > 0

-- Frame conditions (Todo lo demás se congela)
	v2.estado = v.estado
	v2.modo = v.modo
	v2.nivelBateria = v.nivelBateria
	v2.numAsientos = v.numAsientos
	v2.cierreSeguridad = v.cierreSeguridad
	v2.maleteroDisponible = v.maleteroDisponible
	v2.sensores = v.sensores
	v2.pasajeros = v.pasajeros
	v2.zona = v.zona
	v2.ruta = v.ruta
}

-- 5. ASERTOS Y COMPROBACIONES
-- Verificamos que es imposible que un coche se mueva en mantenimiento
assert SinMovimientoEnMantenimiento {
	no v: vAutonomo | v.estado = Mantenimiento and v.velocidad > 0
}
check SinMovimientoEnMantenimiento for 5

-- Verificamos que un coche autónomo en ruta prioritaria jamás falla sus sensores críticos
assert AutonomoSeguroEnRuta {
	all v: vAutonomo | (v.ruta.esPrioritaria = True) implies 
	(all s: v.sensores | s.esCritico = True implies s.estado = OperativoSensor)
}
check AutonomoSeguroEnRuta for 5

-- 6. EXTENSIÓN ORIGRÁFICA (Mejora Creativa)
sig ZonaSierra extends Zona {}

fact RestriccionesSierra {
-- Un vehículo en la sierra gasta más batería, por seguridad no entra con menos de 40%
	all v: vAutonomo | v.zona in ZonaSierra implies v.nivelBateria >= 40

-- Las rutas en la sierra nunca son prioritarias por seguridad orográfica
	all v: vAutonomo | v.zona in ZonaSierra implies v.ruta.esPrioritaria = False
}
pred generarEscenarioValido {}
run generarEscenarioValido for 3 but exactly 1 CentroControl, exactly 2 vAutonomo, exactly 3 Zona

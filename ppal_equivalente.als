-- ==========================================================
-- MODELO ALLOY: Plataforma AutoHuelva
-- Equivalencia máxima con el modelo OCL de la Práctica 1
-- ==========================================================
--
-- LIMITACIONES DE ALLOY (restricciones que no pueden modelarse exactamente):
--
--  [1] TIPO STRING: Los atributos identificadores (idVehiculo, idPasajero,
--      nombre de zona, tipo de sensor, idioma de interfaz, idRuta, etc.)
--      no son modelables porque Alloy no dispone de tipo String primitivo.
--      Se omiten al no participar en ninguna restricción formal.
--
--  [2] TIPO REAL: velocidad, tarifa, distancia, costeFinal y kilometrajeTot
--      se declaran como Int. Es la única aproximación posible en Alloy.
--
--  [3] ENTEROS GRANDES (INV 3, INV 16, INV 17): los literales 5000 (km)
--      y 85 (%) superan el rango del scope por defecto (4 bits: -8..7).
--      Las restricciones son sintácticamente correctas y semánticamente
--      equivalentes al OCL, pero para verificarlas con valores exactos
--      se necesita ampliar el scope: "check ... for 5 but 13 Int"
--      (13 bits cubre hasta 8191). Los 'run' de prueba usan "8 Int"
--      (rango -128..127) como compromiso razonable.
--
--  [4] OPERACIONES CON VALOR DE RETORNO: OCL modela arrancar() y
--      activarModoAutonomo() como funciones Boolean. En Alloy se
--      representan como predicados que describen el caso de éxito
--      (result = true implícito), que es la semántica equivalente.
--
-- ==========================================================

open util/boolean

-- ============================================================
-- 1. ENUMERACIONES
-- ============================================================

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


-- ============================================================
-- 2. CLASES Y ASOCIACIONES
-- ============================================================

-- CentroControl
-- Asociación ZonaCentro (*..1): un centro gestiona varias zonas
sig CentroControl {
    estadoAlerta : one Bool,
    zonas        : set Zona
}

-- Zona
-- Asociación ZonaCarga (1..*): una zona puede contener varias estaciones de carga
sig Zona {
    tipo                  : one TipoZona,
    capacidadMax          : one Int,
    velocidadMaxPermitida : one Int,   -- km/h (atributo OCL; no participa en invariantes directas)
    estaciones            : set EstacionCarga
}

-- EstacionCarga (clase adicional creativa del OCL)
sig EstacionCarga {
    puntosLibres : one Int
}

-- Sensor
-- Asociación VehiculoSensores (1..*): cada sensor pertenece a un único vehículo
sig Sensor {
    esCritico : one Bool,
    estado    : one EstadoSensor
}

-- RegistroMantenimiento (clase adicional creativa del OCL)
-- Asociación VehiculoMantenimiento (1..*): cada registro pertenece a un vehículo
sig RegistroMantenimiento {}

-- InterfazPasajero (clase adicional creativa del OCL)
-- Asociación PasajeroInterfaz (1..1): cada pasajero tiene una interfaz propia
sig InterfazPasajero {
    avisoSeguridad : one Bool
    -- idioma: String --> OMITIDO (tipo String no modelable en Alloy)
}

-- HistoricoTrayectos (clase adicional creativa del OCL)
-- Asociación PasajeroHistorico (1..*): cada histórico pertenece a un pasajero
sig HistoricoTrayectos {
    distancia  : one Int,
    costeFinal : one Int
}

-- Pasajero
sig Pasajero {
    edad               : one Int,
    tipo               : one TipoPasajero,
    tieneEquipajePesado: one Bool,
    tarifa             : one Int,              -- en unidades enteras (aprox. Real)
    interfaz           : one InterfazPasajero, -- PasajeroInterfaz 1..1
    historico          : set HistoricoTrayectos -- PasajeroHistorico 1..*
}

-- Ruta
sig Ruta {
    esPrioritaria : one Bool,
    tiempoEspera  : one Int
}

-- vAutonomo (entidad central del sistema)
sig vAutonomo {
    estado            : one EstadoVehiculo,
    modo              : one ModoConduccion,
    nivelBateria      : one Int,
    numAsientos       : one Int,
    velocidad         : one Int,
    kilometrajeTot    : one Int,    -- aprox. Real; ver limitación [2] y [3]
    cierreSeguridad   : one Bool,
    maleteroDisponible: one Bool,
    disponible        : one Bool,
    -- Asociaciones
    sensores          : set Sensor,           -- VehiculoSensores (1..*)
    pasajeros         : set Pasajero,         -- VehiculoPasajeros (0..*)
    zona              : one Zona,             -- VehiculoZona (*..1)
    ruta              : lone Ruta,            -- VehiculoRuta (1..0..1)
    estacion          : lone EstacionCarga,   -- VehiculoEstacion (*..0..1)
    mantenimientos    : set RegistroMantenimiento -- VehiculoMantenimiento (1..*)
}


-- ============================================================
-- 3. INTEGRIDAD ESTRUCTURAL DE ASOCIACIONES
-- ============================================================

fact IntegridadAsociaciones {

    -- PasajeroInterfaz (1..1): cada InterfazPasajero pertenece a un único Pasajero
    all ip: InterfazPasajero | one p: Pasajero | p.interfaz = ip

    -- PasajeroHistorico (1..*): cada HistoricoTrayectos pertenece a un único Pasajero
    all h: HistoricoTrayectos | one p: Pasajero | h in p.historico

    -- VehiculoSensores (1..*): cada Sensor pertenece a un único vAutonomo
    all s: Sensor | one v: vAutonomo | s in v.sensores

    -- VehiculoPasajeros (0..1 por pasajero): un Pasajero está en a lo sumo un vAutonomo
    all p: Pasajero | lone v: vAutonomo | p in v.pasajeros

    -- VehiculoMantenimiento (1..*): cada RegistroMantenimiento pertenece a un único vAutonomo
    all rm: RegistroMantenimiento | one v: vAutonomo | rm in v.mantenimientos

    -- ZonaCarga (1..*): cada EstacionCarga pertenece a una única Zona
    all e: EstacionCarga | one z: Zona | e in z.estaciones

    -- VehiculoEstacion: la estación asignada al vehículo debe estar en su misma zona
    all v: vAutonomo | some v.estacion implies v.estacion in v.zona.estaciones
}


-- ============================================================
-- 4. INVARIANTES (Equivalentes a los invariantes OCL)
-- ============================================================

fact ReglasDelSistema {

    -- INV 1 [OCL: cierreInfantil]
    -- Si hay algún pasajero menor de 12 años, el cierre de seguridad debe estar activo.
    all v: vAutonomo |
        (some p: v.pasajeros | p.edad < 12) implies v.cierreSeguridad = True

    -- INV 2 [OCL: sensoresCriticos]
    -- En modo autónomo, todos los sensores críticos deben estar operativos.
    all v: vAutonomo |
        v.modo = Autonomo implies
        (all s: v.sensores | s.esCritico = True implies s.estado = OperativoSensor)

    -- INV 3 [OCL: kmMantenimiento]
    -- Más de 5000 km implica estado de mantenimiento.
    -- NOTA [limitación 3]: verificable solo con scope "for 13 Int" o superior.
    all v: vAutonomo |
        v.kilometrajeTot > 5000 implies v.estado = Mantenimiento

    -- INV 4 [OCL: capacidadAsientos]
    -- Un vehículo en movimiento no puede tener más pasajeros que asientos.
    all v: vAutonomo |
        v.velocidad > 0 implies #v.pasajeros <= v.numAsientos

    -- INV 5 [OCL: capacidadVehiculos]
    -- Ninguna zona puede superar su capacidad máxima de vehículos.
    all z: Zona |
        #{v: vAutonomo | v.zona = z} <= z.capacidadMax

    -- INV 6 [OCL: tiempoEsperaMax]
    -- El tiempo de espera de una ruta no puede superar los 30 minutos.
    all r: Ruta |
        r.tiempoEspera <= 30

    -- INV 7 [OCL: maleteroEquipaje]
    -- Si algún pasajero lleva equipaje pesado, el maletero debe estar disponible.
    all v: vAutonomo |
        (some p: v.pasajeros | p.tieneEquipajePesado = True) implies v.maleteroDisponible = True

    -- INV 8 [OCL: limitePeatones]
    -- En zona peatonal, la velocidad no puede superar los 20 km/h.
    all v: vAutonomo |
        v.zona.tipo = Peatonal implies v.velocidad <= 20

    -- INV 9 [OCL: bateriaBaja]
    -- Con batería < 10%, el vehículo no puede llevar pasajeros y debe estar en zona de carga.
    all v: vAutonomo |
        v.nivelBateria < 10 implies (no v.pasajeros and v.zona.tipo = Carga)

    -- INV 10 [OCL: tarifas]
    -- La tarifa de un pasajero Estándar nunca puede ser inferior a la de uno Oro.
    -- (Equivale al OCL que usa allInstances()->any(true), aquí expresado universalmente)
    all p1, p2: Pasajero |
        (p1.tipo = EstandarPasajero and p2.tipo = Oro) implies p1.tarifa >= p2.tarifa

    -- INV 11 [OCL: zonaEmergencia]
    -- Un vehículo en zona de emergencia debe operar en modo manual.
    all v: vAutonomo |
        v.zona.tipo = Emergencia implies v.modo = Manual

    -- INV 12 [OCL: rutaPrioritaria]
    -- Las rutas prioritarias solo pueden asignarse a vehículos en modo autónomo.
    all r: Ruta |
        r.esPrioritaria = True implies
        (all v: vAutonomo | v.ruta = r implies v.modo = Autonomo)

    -- INV 13 [OCL: mantenimientoSinPasajeros]
    -- Un vehículo en mantenimiento no puede llevar pasajeros.
    all v: vAutonomo |
        v.estado = Mantenimiento implies no v.pasajeros

    -- INV 14 [OCL: alertaEmergencia]
    -- El Centro de Control activa la alerta si alguna de sus zonas es de emergencia.
    all cc: CentroControl |
        (some z: cc.zonas | z.tipo = Emergencia) implies cc.estadoAlerta = True

    -- INV 15 [OCL: cargaParado]
    -- Un vehículo en zona de carga debe estar parado.
    all v: vAutonomo |
        v.zona.tipo = Carga implies v.velocidad = 0

    -- INV 16 [OCL: limiteCargaMax]
    -- El nivel de batería no puede superar el 85% (protección del acumulador).
    -- NOTA [limitación 3]: el literal 85 requiere "for 8 Int" como mínimo.
    all v: vAutonomo |
        v.nivelBateria <= 85

    -- INV 17 [OCL: disponibleAlCargar]
    -- Al alcanzar el 85% de batería, el vehículo pasa a disponible automáticamente.
    -- NOTA [limitación 3]: ídem INV 16.
    all v: vAutonomo |
        v.nivelBateria = 85 implies v.disponible = True
}


-- ============================================================
-- 5. CONTRATOS DE OPERACIONES (Pre/Postcondiciones)
-- ============================================================

-- Operación: embarcarPasajero(p: Pasajero)
-- Pre:  el vehículo no está lleno y tiene batería suficiente; p no está a bordo
-- Post: p queda incluido en el conjunto de pasajeros del vehículo
pred embarcarPasajero [v, v2: vAutonomo, p: Pasajero] {
    -- Precondiciones
    #v.pasajeros < v.numAsientos
    v.nivelBateria >= 10
    p not in v.pasajeros

    -- Postcondiciones
    v2.pasajeros = v.pasajeros + p

    -- Frame conditions (todo lo demás permanece igual)
    v2.estado             = v.estado
    v2.modo               = v.modo
    v2.nivelBateria       = v.nivelBateria
    v2.numAsientos        = v.numAsientos
    v2.velocidad          = v.velocidad
    v2.kilometrajeTot     = v.kilometrajeTot
    v2.cierreSeguridad    = v.cierreSeguridad
    v2.maleteroDisponible = v.maleteroDisponible
    v2.disponible         = v.disponible
    v2.sensores           = v.sensores
    v2.zona               = v.zona
    v2.ruta               = v.ruta
    v2.estacion           = v.estacion
    v2.mantenimientos     = v.mantenimientos
}

-- Operación: arrancar() : Boolean
-- Pre:  pasajeros <= asientos, vehículo Operativo, velocidad actual = 0
-- Post: el vehículo está en movimiento (velocidad > 0)
-- NOTA [limitación 4]: se modela el caso de éxito (result = true)
pred arrancar [v, v2: vAutonomo] {
    -- Precondiciones
    #v.pasajeros <= v.numAsientos
    v.estado = Operativo
    v.velocidad = 0

    -- Postcondiciones
    v2.velocidad > 0

    -- Frame conditions
    v2.estado             = v.estado
    v2.modo               = v.modo
    v2.nivelBateria       = v.nivelBateria
    v2.numAsientos        = v.numAsientos
    v2.kilometrajeTot     = v.kilometrajeTot
    v2.cierreSeguridad    = v.cierreSeguridad
    v2.maleteroDisponible = v.maleteroDisponible
    v2.disponible         = v.disponible
    v2.sensores           = v.sensores
    v2.pasajeros          = v.pasajeros
    v2.zona               = v.zona
    v2.ruta               = v.ruta
    v2.estacion           = v.estacion
    v2.mantenimientos     = v.mantenimientos
}

-- Operación: activarModoAutonomo() : Boolean
-- Pre:  todos los sensores críticos están en estado Operativo
-- Post: el vehículo queda en modo Autónomo
-- NOTA [limitación 4]: se modela el caso de éxito; el valor de retorno
--   (Boolean) no es expresable en Alloy, se omite sin pérdida semántica.
pred activarModoAutonomo [v, v2: vAutonomo] {
    -- Precondiciones
    all s: v.sensores | s.esCritico = True implies s.estado = OperativoSensor

    -- Postcondiciones
    v2.modo = Autonomo

    -- Frame conditions
    v2.estado             = v.estado
    v2.nivelBateria       = v.nivelBateria
    v2.numAsientos        = v.numAsientos
    v2.velocidad          = v.velocidad
    v2.kilometrajeTot     = v.kilometrajeTot
    v2.cierreSeguridad    = v.cierreSeguridad
    v2.maleteroDisponible = v.maleteroDisponible
    v2.disponible         = v.disponible
    v2.sensores           = v.sensores
    v2.pasajeros          = v.pasajeros
    v2.zona               = v.zona
    v2.ruta               = v.ruta
    v2.estacion           = v.estacion
    v2.mantenimientos     = v.mantenimientos
}

-- Operación: finalizarCarga() : Boolean
-- Pre:  el vehículo está en zona de Carga y la batería ha alcanzado el 85%
-- Post: el vehículo queda disponible y sin movimiento
pred finalizarCarga [v, v2: vAutonomo] {
    -- Precondiciones
    v.zona.tipo = Carga
    v.nivelBateria = 85   -- NOTA [limitación 3]: requiere "for 8 Int" mínimo

    -- Postcondiciones
    v2.disponible = True
    v2.velocidad  = 0

    -- Frame conditions
    v2.estado             = v.estado
    v2.modo               = v.modo
    v2.nivelBateria       = v.nivelBateria
    v2.numAsientos        = v.numAsientos
    v2.kilometrajeTot     = v.kilometrajeTot
    v2.cierreSeguridad    = v.cierreSeguridad
    v2.maleteroDisponible = v.maleteroDisponible
    v2.sensores           = v.sensores
    v2.pasajeros          = v.pasajeros
    v2.zona               = v.zona
    v2.ruta               = v.ruta
    v2.estacion           = v.estacion
    v2.mantenimientos     = v.mantenimientos
}


-- ============================================================
-- 6. ASERTOS DE VERIFICACIÓN
-- ============================================================

-- Un vehículo en mantenimiento no puede estar en movimiento
-- (derivado de INV 13 + INV 4: Mantenimiento → no pasajeros, velocidad > 0 → pasajeros ≤ asientos)
assert SinMovimientoEnMantenimiento {
    no v: vAutonomo | v.estado = Mantenimiento and v.velocidad > 0
}
check SinMovimientoEnMantenimiento for 5

-- Un vehículo autónomo en ruta prioritaria tiene siempre sus sensores críticos operativos
-- (derivado de INV 12 + INV 2)
assert AutonomoSeguroEnRuta {
    all v: vAutonomo |
        (some v.ruta and v.ruta.esPrioritaria = True) implies
        (all s: v.sensores | s.esCritico = True implies s.estado = OperativoSensor)
}
check AutonomoSeguroEnRuta for 5

-- La alerta del CentroControl siempre está activa ante zonas de emergencia
assert AlertaActiva {
    all cc: CentroControl |
        (some z: cc.zonas | z.tipo = Emergencia) implies cc.estadoAlerta = True
}
check AlertaActiva for 5

-- Un vehículo con batería crítica nunca tiene pasajeros
assert BateriaCriticaSinPasajeros {
    all v: vAutonomo | v.nivelBateria < 10 implies no v.pasajeros
}
check BateriaCriticaSinPasajeros for 5


-- ============================================================
-- 7. EXTENSIÓN OROGRÁFICA (ZonaSierra - mejora creativa)
-- ============================================================

sig ZonaSierra extends Zona {}

fact RestriccionesSierra {
    -- Batería mínima del 40% para operar en zona de sierra
    all v: vAutonomo | v.zona in ZonaSierra implies v.nivelBateria >= 40

    -- Las rutas asignadas en la sierra nunca son prioritarias
    all v: vAutonomo |
        v.zona in ZonaSierra implies
        (some v.ruta implies v.ruta.esPrioritaria = False)
}


-- ============================================================
-- 8. ESCENARIOS DE PRUEBA
-- ============================================================

pred generarEscenarioValido {}

-- Se usa "8 Int" para que los literales 10, 20, 30, 85 sean representables
run generarEscenarioValido for 3 but
    exactly 1 CentroControl,
    exactly 2 vAutonomo,
    exactly 3 Zona,
    exactly 2 Sensor,
    exactly 1 Pasajero,
    8 Int

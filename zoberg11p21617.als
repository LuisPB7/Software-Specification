open util/ordering[Time]

sig Time {}

//--------------------------------------------------------//
//					DEFINED SETS								//
//-------------------------------------------------------//

sig CLIENTS{}
sig DRIVERS {}
sig CARS{}
sig NAMES {}
sig RIDES {}
sig EMAILS {}
sig LICENSES {}
enum ZOBERSERVICE {ZoberY, ZoberWhite} 
enum PLAN {REGULAR, VIP} 


sig zober_client extends CLIENTS{ //R1, R2
	name: one NAMES,
	email: one EMAILS,
	status: PLAN one -> Time, //R4
}


sig zober_driver extends DRIVERS{ //R11, R12
	name: one NAMES,
	license: one LICENSES,
}


sig zober_car extends CARS{ //R18
	owner: one zober_driver, //R19, R20
	setDrivers: zober_driver some->Time,
	service:  ZOBERSERVICE one -> Time, //R24
}


sig zober_ride extends RIDES{ //R29
	car: one zober_car,
	client: one zober_client,
	level: ZOBERSERVICE one -> Time,
	begin: Int,
	end:  Int,
	rating: Int ->Time, //R33
}


one sig Reg_Clients{clients: zober_client -> Time}

one sig Reg_Drivers{drivers: zober_driver -> Time}

one sig Banned_Drivers{banDrivers: zober_driver -> Time}

one sig Reg_Cars{cars: zober_car -> Time}

one sig Reg_Rides{rides: zober_ride -> Time}


//--------------------------------------------------------//
//					INITIALIZATION							//
//-------------------------------------------------------//

pred init[t: Time] { 
	no Reg_Clients.clients.t //R5
    no Reg_Drivers.drivers.t //R14
	no Reg_Cars.cars.t //R25
	no Reg_Rides.rides.t
	no Banned_Drivers.banDrivers.t
	all client: zober_client | client.status.t = REGULAR //R7
	all car: zober_car | car.service.t = ZoberY //R26
	all ride: zober_ride | ride.rating.t = 0 
}

pred noChangeInClientStatus (t,t':Time) {
	all cli: zober_client | cli.status.t' = cli.status.t
}

pred noChangeInRegisteredClients (t,t':Time) {
	Reg_Clients.clients.t' = Reg_Clients.clients.t
}

pred noChangeInRegisteredDrivers(t, t':Time){
	Reg_Drivers.drivers.t' = Reg_Drivers.drivers.t
}

pred noChangeInBannedDrivers(t, t':Time){
	Banned_Drivers.banDrivers.t' = Banned_Drivers.banDrivers.t
}

pred noChangeInRegisteredCars(t, t':Time){
	Reg_Cars.cars.t' = Reg_Cars.cars.t
}

pred noChangeInRegisteredRides(t, t':Time){
	Reg_Rides.rides.t' = Reg_Rides.rides.t
}

pred noChangeInCarService(t, t':Time){
	all car: zober_car | car.service.t' = car.service.t
}

pred noChangeInCarDrivers(t, t':Time){
	all car: zober_car | car.setDrivers.t' = car.setDrivers.t
}

pred noChangeInRideRating(t, t':Time){
	all ride: zober_ride | ride.rating.t' = ride.rating.t
}

pred noChangeInRideLevel(t, t':Time){
	all ride: zober_ride| ride.level.t' = ride.level.t
}


//--------------------------------------------------------//
//					CLIENT OPERATIONS					//
//-------------------------------------------------------//

pred newClient[c: zober_client,  t, t':Time]{
	let clients = Reg_Clients.clients{
		!(c in clients.t) //R6
		no c1,c2:  clients.t' | c1 != c2 and c1.email = c2.email //R3
		c.status.t' = REGULAR //R7
		clients.t' = clients.t + c
	}
    noChangeInClientStatus[t, t'] 
	noChangeInRegisteredDrivers[t, t']
	noChangeInRegisteredCars[t, t']
	noChangeInBannedDrivers[t, t']
	noChangeInCarService[t, t']
	noChangeInCarDrivers[t, t']
	noChangeInRideRating[t, t']
	noChangeInRideLevel[t, t'] 
}

pred removeClient(outClient: zober_client,  t, t':Time){
	let clients = Reg_Clients.clients {
		(outClient in clients.t) //R8
		#(~client[outClient]) = 0 //R36
		clients.t' = clients.t - outClient 
	}

	noChangeInClientStatus[t, t']
	noChangeInRegisteredDrivers[t, t']
	noChangeInRegisteredCars[t, t']
	noChangeInBannedDrivers[t, t']
    noChangeInRegisteredRides[t, t']
	noChangeInCarService[t, t']
	noChangeInCarDrivers[t, t']
	noChangeInRideRating[t, t']
	noChangeInRideLevel[t, t']
}

pred upgradePlan(client: zober_client, t,t':Time){
	client.status.t = REGULAR //R10
	let clients = Reg_Clients.clients{
		client in clients.t //R9
		client.status.t' = VIP
	}

	noChangeInRegisteredClients[t, t']
	noChangeInRegisteredDrivers[t, t']
	noChangeInRegisteredCars[t, t']
	noChangeInBannedDrivers[t, t']
	noChangeInRegisteredRides[t, t']
	noChangeInCarService[t, t']
	noChangeInCarDrivers[t, t']
	noChangeInRideRating[t, t']
	noChangeInRideLevel[t, t']

}


pred downgradePlan(client: zober_client, t,t':Time){
	client.status.t = VIP //R10
	let clients = Reg_Clients.clients{
		client in clients.t //R9
		client.status.t' = REGULAR
	}

	noChangeInRegisteredClients[t, t'] 
	noChangeInRegisteredDrivers[t, t']
	noChangeInRegisteredCars[t, t']
	noChangeInBannedDrivers[t, t']
	noChangeInRegisteredRides[t, t']
	noChangeInCarService[t, t']
	noChangeInCarDrivers[t, t']
	noChangeInRideRating[t, t']
	noChangeInRideLevel[t, t']

}


//--------------------------------------------------------//
//					DRIVER OPERATIONS					//
//-------------------------------------------------------//

pred newDriver(newDriver: zober_driver,  t, t':Time){
 	let drivers = Reg_Drivers.drivers, bdrivers = Banned_Drivers.banDrivers{
		!(newDriver in drivers.t or newDriver in bdrivers.t) //R15, R17
		no d1,d2:drivers.t' | d1 != d2 and d1.license = d2.license //R13
		drivers.t' = drivers.t + newDriver
	}

	noChangeInClientStatus[t, t']
	noChangeInRegisteredClients[t, t']
	noChangeInRegisteredCars[t, t']
	noChangeInBannedDrivers[t, t']
	noChangeInRegisteredRides[t, t']
	noChangeInCarService[t, t']
	noChangeInCarDrivers[t, t']
	noChangeInRideRating[t, t']
	noChangeInRideLevel[t, t']

}

pred removeDriver(outDriver: zober_driver,  t, t':Time){
	let drivers = Reg_Drivers.drivers {
		(outDriver in drivers.t) //R16
		#(~car[~(setDrivers.t)[outDriver]]) = 0 //R40
		drivers.t' = drivers.t - outDriver 
	}

	noChangeInClientStatus[t, t']
	noChangeInRegisteredClients[t, t']
	noChangeInRegisteredCars[t, t']
	noChangeInBannedDrivers[t, t']
	noChangeInRegisteredRides[t, t']
	noChangeInCarService[t, t']
	noChangeInCarDrivers[t, t']
	noChangeInRideRating[t, t']
	noChangeInRideLevel[t, t']

}


pred banDriver(banDriver: zober_driver,  t, t':Time){ //R17
	let drivers = Reg_Drivers.drivers, banDrivers = Banned_Drivers.banDrivers, rides = Reg_Rides.rides, cars = Reg_Cars.cars{
		(banDriver in drivers.t)
		rides.t' = rides.t - ~car[~(setDrivers.t)[banDriver]] //R38
		cars.t' = cars.t - ~owner[banDriver] //R38
		drivers.t'= drivers.t - banDriver
		banDrivers.t' = banDrivers.t + banDriver
	}
	noChangeInClientStatus[t, t']
	noChangeInRegisteredClients[t, t']
	noChangeInRegisteredCars[t, t']
	noChangeInRegisteredRides[t, t']
	noChangeInCarService[t, t']
	noChangeInCarDrivers[t, t'] 
	noChangeInRideRating[t, t']
	noChangeInRideLevel[t, t']
}

//--------------------------------------------------------//
//					CARS OPERATIONS						//
//-------------------------------------------------------//

pred addCar(newCar: zober_car, o: zober_driver,  t, t':Time){
 	let cars = Reg_Cars.cars {
		!(newCar in cars.t)	
		newCar.owner = o
		newCar.setDrivers.t' = o //R21
		newCar.service.t' = ZoberY
		cars.t' = cars.t + newCar
	}
	noChangeInClientStatus[t, t']
	noChangeInRegisteredClients[t, t']
	noChangeInRegisteredDrivers[t, t']
	noChangeInBannedDrivers[t, t']
	noChangeInCarService[t, t'] 
	noChangeInCarDrivers[t, t']
	noChangeInRideRating[t, t']
	noChangeInRideLevel[t, t']
}

pred removeCar(outCar: zober_car,  t, t':Time){
	let cars = Reg_Cars.cars {
		(outCar in cars.t) //R27
		#(~car[outCar]) = 0 //R39
		cars.t' = cars.t - outCar 
	}
	noChangeInClientStatus[t, t']
	noChangeInRegisteredClients[t, t']
	noChangeInRegisteredDrivers[t, t']
	noChangeInBannedDrivers[t, t']
	noChangeInRegisteredRides[t, t']
	noChangeInCarService[t, t']
	noChangeInCarDrivers[t, t']
	noChangeInRideRating[t, t']
	noChangeInRideLevel[t, t']
}

pred addDriverToCar(car: zober_car, inDriver:zober_driver, t,t':Time){
	let cars = Reg_Cars.cars, drivers = Reg_Drivers.drivers {
		(car in cars.t && inDriver in drivers.t) //R22, R28
		#(car.setDrivers.t & drivers.t) <= 2 //R20 
		#(~(setDrivers.t)[inDriver] & cars.t) <= 1 //R23 
		car.setDrivers.t' = car.setDrivers.t + inDriver
	}

	noChangeInClientStatus[t, t']
	noChangeInRegisteredClients[t, t']
	noChangeInRegisteredDrivers[t, t']
	noChangeInRegisteredCars[t, t']	
	noChangeInBannedDrivers[t, t']
	noChangeInRegisteredRides[t, t']
	noChangeInCarService[t, t']		
	noChangeInRideRating[t, t']
	noChangeInRideLevel[t, t'] 

}

pred removeDriverFromCar(car: zober_car, outDriver:zober_driver, t,t':Time){
	let cars = Reg_Cars.cars, drivers = Reg_Drivers.drivers {
		(car in cars.t && outDriver in drivers.t && outDriver !=car.owner ) //R28
		car.setDrivers.t' = car.setDrivers.t - outDriver
	}
	noChangeInClientStatus[t, t']
	noChangeInRegisteredClients[t, t']
	noChangeInRegisteredDrivers[t, t']
	noChangeInRegisteredCars[t, t']	
	noChangeInBannedDrivers[t, t']
	noChangeInRegisteredRides[t, t']
	noChangeInCarService[t, t']		
	noChangeInRideRating[t, t']
	noChangeInRideLevel[t, t']

}

pred upgradeService(car: zober_car, t,t':Time){
	car.service.t = ZoberY
	let cars = Reg_Cars.cars{
		car in cars.t
		car.service.t' = ZoberWhite
	}
	noChangeInClientStatus[t, t']
	noChangeInRegisteredClients[t, t']
	noChangeInRegisteredDrivers[t, t']
	noChangeInRegisteredCars[t, t']		
	noChangeInBannedDrivers[t, t']
	noChangeInRegisteredRides[t, t']
	noChangeInCarDrivers[t, t']
	noChangeInRideRating[t, t']
	noChangeInRideLevel[t, t']

}

pred downgradeService(car: zober_car, t,t':Time){
	car.service.t = ZoberWhite
	let cars = Reg_Cars.cars{
		car in cars.t
		car.service.t' = ZoberY
	}
	noChangeInClientStatus[t, t']
	noChangeInRegisteredClients[t, t']
	noChangeInRegisteredDrivers[t, t']
	noChangeInRegisteredCars[t, t']
	noChangeInBannedDrivers[t, t']
	noChangeInRegisteredRides[t, t']
	noChangeInCarDrivers[t, t']
	noChangeInRideRating[t, t']
	noChangeInRideLevel[t, t']

}

//--------------------------------------------------------//
//					RIDES OPERATIONS						//
//-------------------------------------------------------//

pred newRide(newRide: zober_ride, cli: zober_client, t, t':Time){
    	let rides = Reg_Rides.rides, clients = Reg_Clients.clients{
			!(newRide in rides.t) && (cli in clients.t) && (newRide.begin<newRide.end) //R31 
			(newRide.car in Reg_Cars.cars.t)
			newRide.car.service.t = newRide.level.t // R30
			cli.status.t = VIP => newRide.level.t' = ZoberWhite //R35
			newRide.client = cli
			all rid: ~car[newRide.car] | rid != newRide => newRide.begin > rid.end or newRide.end < rid.begin //R32
	    	cli.status.t = REGULAR => #(~client[cli]) <= 1 //R34 
			rides.t' = rides.t + newRide
		}
	noChangeInClientStatus[t, t']
	noChangeInRegisteredClients[t, t']
	noChangeInRegisteredDrivers[t, t']
	noChangeInBannedDrivers[t, t']
	noChangeInCarDrivers[t, t']
	noChangeInRideRating[t, t']
}


pred cancelRide(cancelledRide: zober_ride, t, t':Time){
 	let rides = Reg_Rides.rides  {
		(cancelledRide in rides.t)
		cancelledRide.rating.t = 0 //R37
		rides.t' = rides.t - cancelledRide
	}
	noChangeInClientStatus[t, t']
	noChangeInRegisteredClients[t, t']
	noChangeInRegisteredDrivers[t, t']
	noChangeInRegisteredCars[t, t']
	noChangeInBannedDrivers[t, t']
	noChangeInCarService[t, t']
	noChangeInCarDrivers[t, t']
	noChangeInRideRating[t, t']
	noChangeInRideLevel[t, t']

}

pred completeRide(ride: zober_ride, grade:Int,  t, t':Time){
	let rides = Reg_Rides.rides {
	(ride in rides.t)
	(grade >= 1 && grade <= 5) => ride.rating.t' = grade //R33
	}
	noChangeInClientStatus[t, t']
	noChangeInRegisteredClients[t, t']
	noChangeInRegisteredDrivers[t, t']
	noChangeInRegisteredCars[t, t']
	noChangeInBannedDrivers[t, t']
	noChangeInRegisteredRides[t, t']	

	noChangeInCarService[t, t']
	noChangeInCarDrivers[t, t']
	noChangeInRideLevel[t, t']

}

//--------------------------------------------------------//
//						RESTRICTIONS							//
//-------------------------------------------------------//

fact {all r: zober_ride | r.begin >= 0 and r.end >= 0 and r.begin < r.end}

fact traces {
	init[first]
	all t: Time-last | let t'=t.next |
		some c: zober_client, d, o: zober_driver, car: zober_car, r: zober_ride, g:Int |
			g >= 1 and g<=5 and
			newClient[c, t, t'] or
			removeClient[c, t, t'] or
			upgradePlan[c, t, t'] or
			downgradePlan[c, t, t'] or
			newDriver[d, t, t'] or
			removeDriver[d, t, t'] or
			banDriver[d, t, t'] or
			addCar[car, o, t, t'] or
			removeCar[car, t, t'] or
			addDriverToCar[car, d, t, t'] or 
			removeDriverFromCar[car, d, t, t'] or
			downgradeService[car, t, t'] or
			upgradeService[car, t, t'] or
	        newRide[r, c, t, t'] or
			cancelRide[r, t, t'] or
			completeRide[r, g, t, t']
}

assert everyClientCanRegister { //R1
	all t: Time, c: zober_client | let t' = t.next | newClient[c,t,t'] => c in Reg_Clients.clients.t'
}

assert everyClientHasNameAndMail{ //R2
	all t: Time, clt: Reg_Clients.clients.t | clt.name in NAMES and clt.email in EMAILS
}

assert everyEmailIsUnique { //R3
	all t: Time, c1, c2: Reg_Clients.clients.t | c1.email = c2.email => c1 = c2
}

assert clientIsRegularOrVIP { //R4
	all t:Time, c: Reg_Clients.clients.t | c.status.t = VIP || c.status.t = REGULAR
}

assert noUsersAtInit { //R5
	no Reg_Clients.clients.first
}

assert newClientCantBeAlreadyRegistered { //R6
	all t: Time, c: zober_client | let t' = t.next | c in Reg_Clients.clients.t => !newClient[c, t, t']
}

assert newClientIsRegular { //R7
	all t: Time, c: zober_client | let t' = t.next | newClient[c, t, t'] => c.status.t' = REGULAR
}

assert onlyRegisteredClientsCanBeRemoved { //R8
	all t: Time, c: zober_client | let t' = t.next | removeClient[c,t,t'] => c in Reg_Clients.clients.t
}

assert onlyRegisteredClientsCanBeUpgraded { //R9
	all t: Time, c: zober_client | let t' = t.next | upgradePlan[c,t,t'] => c in Reg_Clients.clients.t
}

assert onlyRegisteredClientsCanBeDowngraded { //R9
	all t: Time, c: zober_client | let t' = t.next | downgradePlan[c,t,t'] => c in Reg_Clients.clients.t
}

assert onlyRegularClientsCanBeUpgraded { //R10
	all t: Time, c: Reg_Clients.clients.t | let t' = t.next |  upgradePlan[c, t, t'] =>c.status.t = REGULAR
}

assert onlyVIPClientsCanBeDowngraded { //R10
	all t: Time, c: Reg_Clients.clients.t | let t' = t.next | downgradePlan[c, t, t'] => c.status.t = VIP
}

assert everyDriverCanRegister { //R11
	all t: Time, d: zober_driver | let t' = t.next | newDriver[d,t,t'] => d in Reg_Drivers.drivers.t'
}

assert everyDriverHasNameAndLicense{ //R12
	all d: Reg_Drivers.drivers.Time | d.name in NAMES and d.license in LICENSES
}

assert everyLicenseIsUnique { //R13
	all t: Time, d1, d2: Reg_Drivers.drivers.t | d1.license = d2.license => d1 = d2
}

assert noDriversAtInit { //R14
	no Reg_Drivers.drivers.first
}

assert newDriverCantBeAlreadyRegistered { //R15
	all t: Time, d: zober_driver | let t' = t.next | d in Reg_Drivers.drivers.t => !newDriver[d, t, t']
}

assert onlyRegisteredDriversCanBeRemoved { //R16
	all t: Time, d: zober_driver | let t' = t.next | removeDriver[d,t,t'] => d in Reg_Drivers.drivers.t
}

assert driversCanBeBanned{ //R17
	all t:Time, d: zober_driver | let t' = t.next | banDriver[d, t, t'] => (d in Banned_Drivers.banDrivers.t') && (d not in Reg_Drivers.drivers.t')
}

assert everyCarCanRegister { //R18
	all t: Time, car: zober_car, o: zober_driver | let t' = t.next | addCar[car,o,t,t'] => car in Reg_Cars.cars.t'
}

 assert everyCarHasOneOwner { //R19
	all t:Time, car: Reg_Cars.cars.t | #car.owner = 1
}

assert CarHasLessThanThreeDrivers { //R20
	all t:Time, driver: zober_driver, car: Reg_Cars.cars.t | let t' = t.next | addDriverToCar[car, driver, t, t'] => (#(car.setDrivers.t' & Reg_Drivers.drivers.t')<=3 and #(car.setDrivers.t' & Reg_Drivers.drivers.t')>=1)
}

assert ownerCarIsDriverCar{ //R21
	all t:Time, car: Reg_Cars.cars.t, own: zober_driver| let t' = t.next | addCar[car, own, t, t'] => own in car.setDrivers.t'
}

assert carDriversAreRegistered{ //R22
	all t: Time, car: Reg_Cars.cars.t, driver: zober_driver | let  t'= t.next | addDriverToCar[car, driver, t, t'] => driver in Reg_Drivers.drivers.t'
}

assert driverHasMaxTwoCars{ //R23
	all t:Time, driver: zober_driver, car: zober_car | let t' = t.next | addDriverToCar[car, driver, t, t'] => #(~(setDrivers.t)[driver] & Reg_Cars.cars.t) <= 2
}

assert carProvidesZoberYOrZoberWhite { //R24
	all t:Time, car: Reg_Cars.cars.t | car.service.t = ZoberY || car.service.t = ZoberWhite
}

assert noCarsAtInit { //R25
	no Reg_Cars.cars.first
}

assert initialCarServiceIsZoberY { //R26
	all t: Time, car: zober_car, o:zober_driver | let t' = t.next | addCar[car, o, t, t'] => car.service.t' = ZoberY
}

assert onlyRegisteredCarsCanBeRemoved { //R27
	all t: Time, car: zober_car | let t' = t.next | removeCar[car,t,t'] => car in Reg_Cars.cars.t
}

assert onlyRegDriversCanBeAssociatedToACar { //R28
	all t:Time, car: zober_car, d:zober_driver | let t'= t.next | addDriverToCar[car,d,t,t'] => d in Reg_Drivers.drivers.t && removeDriverFromCar[car,d,t,t'] => d in Reg_Drivers.drivers.t
}

assert everyRideHasClientAndTimeFrameAndServiceAndCar{ //R29
	all t:Time, ride: Reg_Rides.rides.t | ride.car in CARS and ride.client in CLIENTS and ride.level.t in ZOBERSERVICE and 
															ride.begin in Int  and ride.end in Int and ride.rating in Int->Time
}

assert rideCarHasRightService{ //R30
	all t:Time, cli:Reg_Clients.clients.t, ride: Reg_Rides.rides.t | let t' = t.next | newRide[ride,cli, t, t'] => ride.level = ride.car.service
}

assert rideIsWellFormed{ //R31
	all t:Time, ride:Reg_Rides.rides.t |  ride.begin < ride.end
}

assert noOverlappingRides{ //R32
	all t:Time, cli:Reg_Clients.clients.t, ride: Reg_Rides.rides.t  | let t' = t.next | newRide[ride, cli, t, t'] => all rid: ~car[ride.car] | ride.begin > rid.end or ride.end < rid.begin
}

assert rideHasProperRating{ //R33
	all t:Time, ride:Reg_Rides.rides.t, grade: Int | let t' = t.next |   grade <= 5 and grade >= 1 => ((completeRide[ride, grade, t, t'])  =>  (ride.rating.t' <= 5 and ride.rating.t' >= 1 ))
}

assert regularClientHasAtMostTwoRides{ //R34
	all t:Time, ride: Reg_Rides.rides.t , cli: zober_client | let t' = t.next | newRide[ride, cli,t, t'] => #(~client[cli] & Reg_Rides.rides.t) <= 2
}

assert VIPClientsZoberWhite{ //R35
	all t:Time, ride: Reg_Rides.rides.t , client: zober_client | let t' = t.next | newRide[ride, client,t, t'] => (client.status.t = VIP => ride.level.t = ZoberWhite)
}

assert clientsWithRidesCantBeRemoved{ //R36
	all t:Time, cli: Reg_Clients.clients.t | let t' = t.next | #(~client[cli]) != 0 => !removeClient[cli, t, t']
}

assert nonCompletedRideCanBeCancelled{ //R37
	all t:Time, ride: Reg_Rides.rides.t | let t' = t.next | cancelRide[ride, t, t'] => ride.rating.t' = 0 
}

assert ridesAndCarsFromBannedDriversAreRemoved{ //R38
	all t:Time, driver: Reg_Drivers.drivers.t| let t' = t.next | banDriver[driver, t, t'] => #(~car[~(setDrivers.t)[driver]] & Reg_Rides.rides.t) = 0 and #(~owner[driver] & Reg_Cars.cars.t) = 0
}

assert carWithReservationsCantBeRemoved{ //R39
	all t:Time, c: Reg_Cars.cars.t | let t' = t.next |removeCar[c, t, t'] => #(~car[c]) = 0
}

assert ownerCantBeRemovedIfPendingReservations{ //R40
	all t:Time, d: Reg_Drivers.drivers.t | let t' = t.next | removeDriver[d, t, t'] => #(~car[~(setDrivers.t)[d]]) = 0
}


//--------------------------------------------------------//
//							CHECKS								//
//-------------------------------------------------------//

check everyClientCanRegister for 10

check everyClientHasNameAndMail for 10

check everyEmailIsUnique for 10

check clientIsRegularOrVIP for 10

check noUsersAtInit for 10

check newClientCantBeAlreadyRegistered for 10

check newClientIsRegular for 10

check  onlyRegisteredClientsCanBeRemoved for 10

check  onlyRegisteredClientsCanBeUpgraded for 10

check  onlyRegisteredClientsCanBeDowngraded for 10

check  onlyRegularClientsCanBeUpgraded for 10

check  onlyVIPClientsCanBeDowngraded for 10

check everyDriverCanRegister for 10

check everyDriverHasNameAndLicense for 10

check everyLicenseIsUnique for 10

check noDriversAtInit for 10

check newDriverCantBeAlreadyRegistered  for 10

check onlyRegisteredDriversCanBeRemoved for 10

check driversCanBeBanned for 10

check everyCarCanRegister for 10

check everyCarHasOneOwner  for 10

check CarHasLessThanThreeDrivers for 10

check ownerCarIsDriverCar for 10

check carDriversAreRegistered for 10

check driverHasMaxTwoCars for 10

check carProvidesZoberYOrZoberWhite for 10

check noCarsAtInit for 10

check initialCarServiceIsZoberY  for 10

check onlyRegisteredCarsCanBeRemoved  for 10

check onlyRegDriversCanBeAssociatedToACar for 10

check everyRideHasClientAndTimeFrameAndServiceAndCar for 10

check rideCarHasRightService for 10

check rideIsWellFormed for 10

check noOverlappingRides for 10

check rideHasProperRating for 10

check regularClientHasAtMostTwoRides for 10

check VIPClientsZoberWhite for 10

check clientsWithRidesCantBeRemoved for 10

check  nonCompletedRideCanBeCancelled for 10

check ridesAndCarsFromBannedDriversAreRemoved for 10

check carWithReservationsCantBeRemoved for 10

check ownerCantBeRemovedIfPendingReservations for 10  
 

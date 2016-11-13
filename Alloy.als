open util/boolean

//SIGNATURES

sig Code{}
 
sig Position{}

sig User{}

abstract sig BatteryLevel{}

one sig LowLevel extends BatteryLevel{} // battery level between 0% and 20%
one sig MediumLevel extends BatteryLevel{} // battery level between 21% and 99%
one sig HighLevel extends BatteryLevel{} // battery level equal to 100%
one sig MaxLevel extends BatteryLevel{} // battery level equal to 100%

sig Car{
	code: Code,
	position: Position,
	available: Bool, 
	batteryLevel: BatteryLevel,
	inCharge: Bool
}{
	inCharge=True => batteryLevel!=MaxLevel
}

sig Ride{
	reservation: Reservation,
	driver: User,
	car: Car,
	numberPassenger: Int,
	ended: Bool,
	moreThan3km: Bool,
	inCharge: Bool,
	endBatteryLevel: BatteryLevel
}
{
	inCharge=True => moreThan3km=False
	moreThan3km=True =>	inCharge=False
 	numberPassenger>=0 and numberPassenger<=4
}

sig Reservation{
	car: Car,
	user: User,
	timerEnded: Bool,
	deleted: Bool
}

sig Availability{}

sig PowerGridStation{
	position: Position,
	cars: set Car, 
	availability: Availability
}

one sig SafeArea{
	area: set Position
}

sig Operator{}

sig Operation{
	operator: Operator,
	car: Car,
	ended: Bool
}

//FACTS

//cars in a power grid station are in charge or have just been charged
fact carInAPowerGridStation{
	all p:PowerGridStation | all c:Car | c in p.cars => ((c.inCharge=True or (c.inCharge=False and c.batteryLevel=MaxLevel)))
}

//one car could be at most in one power grid station
fact carInPowerGridStation{
	all c:Car | lone p:PowerGridStation | c in p.cars	
}

//available cars must not be involved in an operation or in a ride or in charge
fact availableCars{
	all c:Car |	c.available=True => 
			c.inCharge=False and (no o: Operation | c=o.car and o.ended=False)
				and (no r: Ride | c= r.car and r.ended=False)
}

//unavailable cars 
fact unavailableCars{
	all c:Car| c.available=False =>
		(c.inCharge=True and ((no o: Operation | c=o.car and o.ended=False) and (no r: Ride | c= r.car and r.ended=False))) or 
		((one o: Operation | c=o.car and o.ended=False) and (c.inCharge=False and (no r: Ride | c= r.car and r.ended=False))) or
		((one r: Ride | c= r.car and r.ended=False) and (c.inCharge=False and (no o: Operation | c=o.car and o.ended=False)))
}



//available cars must have the battery level that isn't low
fact batteryLevelAvailableCars{
	all c: Car | (c.available=True) => c.batteryLevel!=LowLevel
}

//available cars must be in a safe area
fact availableCarsInASafeArea{
	all c: Car | (c.available=True) =>
			( some s: SafeArea | c.position in s.area)
}

// car codes are unique
fact uniqueCodes{
	all c1,c2: Car | (c1 != c2) => c1.code != c2.code
}

// two cars cannot have the same position
fact twoCarWithSamePosition{
	all c1,c2: Car | (c1!=c2) => c1.position!=c2.position 
}

// if a car is in charge, it exists one power grid station that contains the car
fact carsInCharging{
	all c: Car | c.inCharge=True =>
			(one p:PowerGridStation | c in p.cars)
}

//for each user exists at most one ride that is not ended
fact oneRideNotEnded{
	all u:User | lone r:Ride | r.driver=u and r.ended=False
}

//each reservation has at most one ride
fact reservationOneRide{
	all r:Reservation | lone r1:Ride | r1.reservation=r
}

//each deleted reservation has not a ride and his timer is not ended
fact deletedReservation{
	all r: Reservation | (r.timerEnded=False and
				(no r1: Ride | r=r1.reservation)) <=> r.deleted=True
}

//each ride has a reservation whose timer is not ended
fact {
	all r: Ride | r.reservation.timerEnded=False
}

// for each (ride, reservation) car and user must be the same
fact sameCarUser{
	all r: Ride | r.driver=r.reservation.user  and r.car=r.reservation.car
}

//each power grid station is in a safe area
fact powerGridStationInASafeArea{
	all p:PowerGridStation |
			one s:SafeArea | p.position in s.area
}

//two power grid stations cannot have the same position
fact twoPowerGridStationWithSamePosition{
	all p1,p2: PowerGridStation | (p1!=p2) => p1.position!=p2.position 
}

//no operator without operation
fact NoOperationWithoutOperator{
	all o:Operator | one o2:Operation | o2.operator=o
}

//no availability without power grid station
fact NoAvailabilityWithoutPowerStation{
	all a:Availability| one  p:PowerGridStation  | a=p.availability
}

//no user without reservation
fact noUserWithoutReservation{
	all u:User | some r:Reservation | r.user=u
}

//each operator could have at most one operation that is not ended
fact oneOperationNotEnded{
	all o:Operator | lone o1:Operation | o1.operator=o and o1.ended=False
}

//each not ended operation must have different operator and different car
fact differentOperatorAndCars{
	no o1,o2:Operation | o1.ended=False and o2.ended=False and o1!=o2 and o1.operator=o2.operator and o1.car=o2.car
}

// one car could have at most one operation that is not ended
fact oneCareOneOperationNotEnded{
	all c:Car | lone o: Operation | o.car=c and o.ended=False
}

//cars in a power grid station are in a safe are
fact carPowerGridSafeArea{
	all c:Car | all p:PowerGridStation | c in p.cars => (one s:SafeArea | c.position in s.area)
}

//ASSERTION

//check if different ride not already ended has different car
assert DifferentCarsForReservation{
	no r1,r2:Ride | ( r1.ended=False and r2.ended=False and r1.car=r2.car and r1!=r2)
}

check DifferentCarsForReservation

//check if different operation not already ended has different operator
assert DifferentOperationForOperator{
	no o1,o2:Operation | (o1!=o2 and o1.ended=False and o2.ended=False and o1.operator=o2.operator)
}

check DifferentOperationForOperator

//check if different operation not already ended has different cars
assert DifferentCarsForOperation{
	no o1,o2:Operation | (o1!=o2 and o1.ended=False and o2.ended=False and o1.car=o2.car)
}

check DifferentCarsForOperation

// check if all available cars are in the safe area
assert allCarInSafeArea{
	no c:Car | c.available=True and one s:SafeArea | c.position not in s.area
}
check allCarInSafeArea

//check that eac car has a unique code
assert noSameCode{
	no c1,c2:Car | c1!=c2 and c1.code=c2.code
}
check noSameCode

//check that doesn't exists a ride if the associated reservation is deleted
assert NoRideWithDeletedReservation{
	no r:Ride | r.reservation.deleted=True
}
check NoRideWithDeletedReservation


//PREDICATES

// user reserved a car but the timer is ended, and so make another reservation
pred timerEndedAndRide{
	one u:User | some r:Reservation | u=r.user and r.timerEnded=True and (one r1:Ride| r1.driver=u )
	#Ride=1
	#Reservation=2
	#User=1
	#Operator=0
}

run timerEndedAndRide 

//user deletes a reservation
pred deleteReservation{
	one u:User | one r:Reservation | r.user=u and r.deleted=True
	#Ride=1
	#Reservation=2
	#User=1
	#Operator=0
}

run deleteReservation

//when users can have 30% of discount
pred  ThirtyPercentDiscount{
	one r:Ride | (r.ended=True and r.inCharge=True) 
	#User=1
	#Ride=1
}

run ThirtyPercentDiscount

//when users can have 20% of discount
pred  TwentyPercentDiscount{
	one r:Ride | (r.ended=True and (r.car.batteryLevel=HighLevel or r.car.batteryLevel=MaxLevel)
					and r.inCharge=False)
	#User=1
	#Ride=1
}

run TwentyPercentDiscount

//when users can have 10% of discount
pred  TenPercentDiscount{
	all r:Ride | (r.ended=True and r.numberPassenger>=2 and 
	(r.endBatteryLevel!=HighLevel and r.endBatteryLevel!=MaxLevel)
					and  r.inCharge=False)
	#User=1
	#Ride=1
}

//run TenPercentDiscount

pred ThirtyPercentFee{
	all r:Ride | (r.ended=True and (r.endBatteryLevel=LowLevel or r.moreThan3km=True))
	#User=1
	#Ride=1
}

//run ThirtyPercentFee

pred show{

}

//run show



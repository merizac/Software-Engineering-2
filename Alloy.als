open util/boolean

//Signatures

sig Code{}
 
sig Position{}

sig User{}

abstract sig BatteryLevel{}

one sig LowLevel extends BatteryLevel{} // battery level between 0% and 20%
one sig MediumLevel extends BatteryLevel{} // battery level between 21% and 99%
one sig HighLevel extends BatteryLevel{} // battery level equal to 100%

sig Car{
	code: Code,
	position: one Position,
	available: Bool, 
	batteryLevel: BatteryLevel,
	inCharge: Bool
}{
	inCharge=True => batteryLevel!=HighLevel
}

//cars in a power grid station are in charge or have just been charged
fact carInAPowerGridStation{
	all p:PowerGridStation | all c:Car | c in p.cars and (c.inCharge=True or c.inCharge=False and c.batteryLevel=HighLevel)
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
		(c.inCharge=True => (no o: Operation | c=o.car and o.ended=False) and (no r: Ride | c= r.car and r.ended=False)) and
		((one o: Operation | c=o.car and o.ended=False) => c.inCharge=False and (no r: Ride | c= r.car and r.ended=False)) and
		((one r: Ride | c= r.car and r.ended=False) =>c.inCharge=False and (no o: Operation | c=o.car and o.ended=False))
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

sig Ride{
	reservation: one Reservation,
	driver: one User,
	car: one Car,
	ended: Bool
}

//for each user exists at most one ride that is not ended
fact oneRideNotEnded{
	all u:User | lone r:Ride | r.driver=u and r.ended=False
}

sig Reservation{
	car: one Car,
	user: one User,
	timerEnded: Bool,
	deleted: Bool
}

//each reservation has at most one ride
fact reservationOneRide{
	all r:Reservation | lone r1:Ride | r1.reservation=r
}

//each deleted reservation has not a ride and his timer is not ended
fact deletedReservation{
	all r: Reservation | (r.timerEnded=False and
				(no r1: Ride | r in r1.reservation)) <=> r.deleted=True
}

//each ride has a reservation whose timer is not ended
fact {
	all r: Ride | r.reservation.timerEnded=False
}

// for each (ride, reservation) car and user must be the same
fact sameCarUser{
	all r: Ride | r.driver=r.reservation.user  and r.car=r.reservation.car
}

sig Availability{}

sig PowerGridStation{
	position: one Position,
	cars: set Car, 
	availability: Availability
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

one sig SafeArea{
	area: set Position
}

sig Operator{}

sig Operation{
	operator: Operator,
	car: Car,
	ended: Bool
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

pred show{
}
run show

//predicates


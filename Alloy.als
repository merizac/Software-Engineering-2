open util/boolean

//Signatures

sig Code{}
 
sig Position{}

sig User{
//	reservation: set Reservation controllo incrociato??
}

abstract sig BatteryLevel{}

one sig LowLevel extends BatteryLevel{}
one sig MediumLevel extends BatteryLevel{}
one sig HighLevel extends BatteryLevel{}

sig Car{
	code: Code,
	position: one Position,
	available: Bool, 
	batteryLevel: BatteryLevel,
	inCharge: Bool
}{
	available=True => inCharge=False and
	inCharge=True => batteryLevel!=HighLevel
}

//available cars must have the battery level isn't low
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

pred show{}
run show

//predicates


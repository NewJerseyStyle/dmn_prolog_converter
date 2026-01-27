% Discount Calculation Decision
% Calculates customer discount based on loyalty status and order amount

% Rule 1: VIP customers get 20% discount
calculate_discount(Customer, OrderAmount, Discount) :-
    LoyaltyStatus = vip,
    Discount = 20.

% Rule 2: Premium customers with large orders get 15% discount
calculate_discount(Customer, OrderAmount, Discount) :-
    LoyaltyStatus = premium,
    OrderAmount >= 1000,
    Discount = 15.

% Rule 3: Premium customers with small orders get 10% discount
calculate_discount(Customer, OrderAmount, Discount) :-
    LoyaltyStatus = premium,
    OrderAmount < 1000,
    Discount = 10.

% Rule 4: Standard customers with large orders get 5% discount
calculate_discount(Customer, OrderAmount, Discount) :-
    LoyaltyStatus = standard,
    OrderAmount >= 500,
    Discount = 5.

% Rule 5: Standard customers with small orders get no discount
calculate_discount(Customer, OrderAmount, Discount) :-
    LoyaltyStatus = standard,
    OrderAmount < 500,
    Discount = 0.

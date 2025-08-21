print("--- Data Types ---");
let an_integer = 10;
let a_float = 3.14;
let a_string = "Hello, Weasel!";
let a_boolean = true;

print(an_integer);
print(a_float);
print(a_string);
print(a_boolean);



print("--- Arithmetic ---");
let x = 20;
let y = 5;
print(x + y);
print(x - y);
print(x * y);
print(x / y);
print(-x);



print("--- Logic and Comparison ---");
print(x > y);
print(x < y);
print(x == 20);
print(y not= 5);
print(a_boolean and not false);
print(false or true);



print("--- If/Else ---");
if (an_integer > 5) {
    print("Integer is greater than 5.");
} else {
    print("Integer is not greater than 5.");
}

if (not a_boolean) {
    print("This should not print.");
} else {
    print("This should print.");
}



print("--- While Loop ---");
let counter = 0;
while (counter < 5) {
    counter = counter + 1;
    if (counter == 2) {
        print("Skipping 2 with continue.");
        continue;
    }
    if (counter == 4) {
        print("Breaking at 4.");
        break;
    }
    print(counter);
}



print("--- Arrays ---");
let my_array = [10, 20, 30, 40, 50];
print("Original array:");
print(my_array);
print("Element at index 2:");
print(my_array[2]);


my_array[2] = 35;
print("After modification:");
print(my_array);
print(my_array[2]);



print("--- Built-in Functions ---");
print("The sum of 1, 2, 3, 4, 5 is:");
print(sum(1, 2, 3, 4, 5));



print("--- Test Complete ---");

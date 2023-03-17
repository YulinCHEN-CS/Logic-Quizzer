import tkinter as tk
from tkinter import messagebox

# create a 2D array of truth table values
truth_table = [[0, 0, 0],
               [0, 1, 1],
               [1, 0, 1],
               [1, 1, 0]]

# initialize tkinter
root = tk.Tk()
root.title("Truth Table Quiz")

first_variable = "A"
second_variable = "~A"
result = "A&~A"
# create a table with custom headers
header_labels = [first_variable, second_variable, result]
for i, header in enumerate(header_labels):
    tk.Label(root, text=header, relief=tk.RIDGE, width=15).grid(row=0, column=i)

# create input boxes for the last column of the table
input_boxes = []
for i in range(len(truth_table)):
    box = tk.Entry(root, width=15)
    box.grid(row=i+1, column=2)
    input_boxes.append(box)

# fill in the first two columns with truth table values
for i, row in enumerate(truth_table):
    for j, value in enumerate(row):
        if j < 2:
            tk.Label(root, text=value, relief=tk.RIDGE, width=15).grid(row=i+1, column=j)

# create submit button
def check_answers():
    user_answers = [box.get() for box in input_boxes]
    correct_answers = [str(row[2]) for row in truth_table]
    if user_answers == correct_answers:
        messagebox.showinfo("Result", "Correct!")
    else:
        messagebox.showinfo("Result", f"Incorrect. Correct answers: {correct_answers}")

tk.Button(root, text="Submit", command=check_answers).grid(row=len(truth_table)+1, column=1)

root.mainloop()


if __name__ == "__main__":
    root.mainloop()
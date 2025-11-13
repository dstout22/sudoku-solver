const gridContainer = document.getElementById('sudoku-grid');

//cycles through each item in the grid container (all 81 squares)
for (let row = 0; row < 9; row ++){
    for (let col = 0; col < 9; col++){
        const input = document.createElement('input');
        input.type = 'text';
        //makes sure each square can only take in one character
        input.maxLength = 1;
        //stores the cells coordinates
        input.dataset.row = row;
        input.dataset.col = col;

        input.addEventListener('input', () => {
        if (!/^[1-9]$/.test(input.value)){
        //resets the input value to a space if the character input
        //is not a number between 1 and 9
        input.value = '';
        }
        })

        gridContainer.appendChild(input);
    }
}

//calls the solve function when the solve button is clicked
document.getElementById('solve-btn').addEventListener('click', solve);

//implements the solve function
function solve(){

  let grid = []; 
  const numCols = 9;

  //gets the value from each grid and appends it to a 2D array of the grid values
  for (let row = 0; row < 9; row ++){
    let rowGrid = [];
    for (let col = 0; col < 9; col++){
        
        const value = gridContainer.children[row * numCols + col].value;
        rowGrid.push(value);

    }
    grid.push(rowGrid);
  }

  const result = JSON.stringify(grid);

  fetch('/solve', {
    method: 'POST',                       
    headers: { 'Content-Type': 'application/json' },
    body: result
  })
    .then(response => response.json())
    .then(data => {
      let div = document.getElementById("Unsat-div");
      if (div){
        div.style.display = "none";
      }
      console.log('Response from backend:', data);
      const solvedValues = data.values;
      if (data === 'unsat' || data.status === 'unsat') {
        let div = document.createElement("div");
        div.id = "Unsat-div";
        div.innerText = "Unsatisfiable";
        div.style.color = 'red';
        div.classList.add('dynamic-satisfiability');
        document.body.appendChild(div);
        return;
      }
      for (let i = 0; i < 81; i++) {
        if (gridContainer.children[i].value === ''){
          gridContainer.children[i].value = solvedValues[i];
          gridContainer.children[i].style.color = 'green'; 
        }
      }
    })
    .catch(err => console.error('Error:', err));
}

//calls the reset function when the reset button is clicked
document.getElementById('reset-btn').addEventListener('click', reset);

function reset(){
  let div = document.getElementById("Unsat-div");
  if (div){
    div.style.display = "none";
  }
  for (let i = 0; i < 81; i++) {
    if (gridContainer.children[i].value !== ''){
      gridContainer.children[i].value = '';
      gridContainer.children[i].style.color = 'black'; 
    }
  }
}
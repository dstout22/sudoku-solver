// Load Node's built-in 'http' module
const http = require('http');
const fs = require('fs');
const path = require('path');
const {execFile} = require('child_process');
const { stdout } = require('process');

// Pick a port to run the server on
const PORT = 3000;

// Create a basic server that responds to any request
const server = http.createServer((req, res) => {
  
  if(req.method == 'POST' && req.url == '/solve'){

  //this will concatenate the "chunks" of data coming in
  let body = '';

  req.on ('data', chunk => {
    body += chunk.toString();
  });

  req.on ('end', () => {

    try {
        const gridData = JSON.parse(body);
        console.log('Received grid:', gridData);

        //resets the file with only the necessary static components (removes old data)
        const basePath = __dirname;
        const content = fs.readFileSync(path.join(basePath, 'solver.smt2'), 'utf8');
        let parts = content.split('; *Dynamic Portion*');
        const updated = parts[0];
        fs.writeFileSync(path.join(basePath, 'solver.smt2'), updated); 

        fs.appendFileSync('solver.smt2', '; *Dynamic Portion*\n');

        //adds each assert statement to the z3 smt file
        for (let row = 0; row < 9; row++){
          for (let col = 0; col < 9; col++){
            let current = gridData[row][col];
            if (current != ''){
              fs.appendFileSync('solver.smt2', '(assert (= (a ' + row + ' ' + col + ') ' + parseInt(current) + '))\n');
            }
          }
        }

        //adds the check-sat and get-value statements to teh z3 smt file
        fs.appendFileSync('solver.smt2', '(check-sat)\n');
        fs.appendFileSync('solver.smt2', `(get-value (
          (a 0 0) (a 0 1) (a 0 2) (a 0 3) (a 0 4) (a 0 5) (a 0 6) (a 0 7) (a 0 8)
          (a 1 0) (a 1 1) (a 1 2) (a 1 3) (a 1 4) (a 1 5) (a 1 6) (a 1 7) (a 1 8)
          (a 2 0) (a 2 1) (a 2 2) (a 2 3) (a 2 4) (a 2 5) (a 2 6) (a 2 7) (a 2 8)
          (a 3 0) (a 3 1) (a 3 2) (a 3 3) (a 3 4) (a 3 5) (a 3 6) (a 3 7) (a 3 8)
          (a 4 0) (a 4 1) (a 4 2) (a 4 3) (a 4 4) (a 4 5) (a 4 6) (a 4 7) (a 4 8)
          (a 5 0) (a 5 1) (a 5 2) (a 5 3) (a 5 4) (a 5 5) (a 5 6) (a 5 7) (a 5 8)
          (a 6 0) (a 6 1) (a 6 2) (a 6 3) (a 6 4) (a 6 5) (a 6 6) (a 6 7) (a 6 8)
          (a 7 0) (a 7 1) (a 7 2) (a 7 3) (a 7 4) (a 7 5) (a 7 6) (a 7 7) (a 7 8)
          (a 8 0) (a 8 1) (a 8 2) (a 8 3) (a 8 4) (a 8 5) (a 8 6) (a 8 7) (a 8 8)
          ))`);

        //Call Z3
        execFile('z3', ['solver.smt2'], (error, stdout, stderr) => {
          if (error){
            //logs that the input was not received successfully
            console.error('input probably unsat');

            res.writeHead(200, { 'Content-Type': 'application/json' });
            res.end(JSON.stringify('unsat'));
            return;
          }

          //logs that the input was received successfully
          console.log('input received');
          console.log(stdout);

           //splits stdout into separate lines to be parsed
          const lines = stdout.trim().split('\n');
         
          //returns unsat if the result is not sat
          if (lines[0] !== 'sat') {
            res.writeHead(200, { 'Content-Type': 'application/json' });
            res.end(JSON.stringify({ status: lines[0] }));
            return;
          }
        
        //removes the first item in the array ("sat")
        lines.shift();

        //stores each of the values in the grid in order
        let values = [];
        for (let i = 0; i < lines.length; i++){
          values[i] = lines[i].at(10);
        }

        // Return to frontend
        res.writeHead(200, { 'Content-Type': 'application/json' });
        res.end(JSON.stringify({ status: 'sat', values }));

        });

      } catch (err) {
        res.writeHead(400, { 'Content-Type': 'application/json' });
        res.end(JSON.stringify({ error: 'Invalid JSON' }));
        return;
      } 

  });

  return;
}

// Serve frontend files
  if (req.method === 'GET') {
    let filePath = req.url === '/' ? './index.html' : `.${req.url}`;
    const ext = path.extname(filePath);

    // Set the content type based on file extension
    let contentType = 'text/html';
    if (ext === '.js') contentType = 'application/javascript';
    else if (ext === '.css') contentType = 'text/css';

    // Read and send the requested file
    fs.readFile(filePath, (err, data) => {
      if (err) {
        res.writeHead(404, { 'Content-Type': 'text/plain' });
        res.end('404: File not found');
        return;
      }
      res.writeHead(200, { 'Content-Type': contentType });
      res.end(data);
    });
  }

});

// Start the server
server.listen(PORT, () => {
  console.log(`Server running at http://localhost:${PORT}`);
});

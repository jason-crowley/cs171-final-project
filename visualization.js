const d3 = require('d3')
d3.select(svg).selectAll("*").remove();

function fillPieces(row, col, color) {
    if (color == "red") // Red L-Piece
        d3.select(svg)
            .append("rect")
            .style("fill", "red")
            .attr("x", 5+(row*75))
            .attr("y", 5+(col*75))
            .attr('width', 75)
            .attr('height', 75)
    if (color == "blue") // Blue L-Piece
        d3.select(svg)
            .append("rect")
            .style("fill", "blue")
            .attr("x", 5+(row*75))
            .attr("y", 5+(col*75))
            .attr('width', 75)
            .attr('height', 75)
    if (color == "gray") // Neutral 
         d3.select(svg)
            .append("rect")
            .style("fill", "gray")
            .attr("x", 5+(row*75))
            .attr("y", 5+(col*75))
            .attr('width', 75)
            .attr('height', 75)
}   

function printState() {
  drawGrid()
  // Iterate through pieces in Game (red, blue, neutral) and call fillPieces
}

function drawGrid() {
  d3.select(svg)
    .append('rect')
    .attr('x', 5)
    .attr('y', 5)
    .attr('width', 300)
    .attr('height', 300)
    .attr('stroke-width', 2)
    .attr('stroke', 'black')
    .attr('fill', 'transparent');
  for(i = 1; i < 4; i++)
    d3.select(svg)
      .append('line')
      .style("stroke", "black")
      .style("stroke-width", 3)
      .attr("x1", 5)
      .attr("y1", 5 + 75*i)
      .attr("x2", 305)
      .attr("y2", 5 + 75*i); 
  for(i = 1; i < 4; i++)
    d3.select(svg)
      .append('line')
      .style("stroke", "black")
      .style("stroke-width", 3)
      .attr("x1", 5 + 75*i)
      .attr("y1", 5)
      .attr("x2", 5 + 75*i)
      .attr("y2", 305); 
}

printState()
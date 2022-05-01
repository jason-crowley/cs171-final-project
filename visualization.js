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
    if (color == "neutral") // Neutral 
         d3.select(svg)
            .append("rect")
            .style("fill", "gray")
            .attr("x", 5+(row*75))
            .attr("y", 5+(col*75))
            .attr('width', 75)
            .attr('height', 75)
}   

function printState() {
  // Iterate through pieces in Game (red, blue, neutral) and call fillPieces
  const red = instances[currentInstance].field("red").tuples()
  const blue = instances[currentInstance].field("blue").tuples()
  const neutral = instances[currentInstance].field("neutral").tuples()

  for (i=0; i<4; i++){
    fillPieces(parseInt(red[i].atoms(0)[1].id()) + 2, parseInt(red[i].atoms(0)[2].id()) + 2, "red")
    // not letting me fill blue in the loop for some reason
  }

  fillPieces(parseInt(blue[0].atoms(0)[1].id()) + 2, parseInt(blue[0].atoms(0)[2].id()) + 2, "blue")
  fillPieces(parseInt(blue[1].atoms(0)[1].id()) + 2, parseInt(blue[1].atoms(0)[2].id()) + 2, "blue")
  fillPieces(parseInt(blue[2].atoms(0)[1].id()) + 2, parseInt(blue[2].atoms(0)[2].id()) + 2, "blue")
  fillPieces(parseInt(blue[3].atoms(0)[1].id()) + 2, parseInt(blue[3].atoms(0)[2].id()) + 2, "blue")

  for (i=0; i<2; i++) {
    fillPieces(parseInt(neutral[i].atoms(0)[1].id()) + 2, parseInt(neutral[i].atoms(0)[2].id()) + 2, "neutral")
  }
  
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

drawGrid()
printState()
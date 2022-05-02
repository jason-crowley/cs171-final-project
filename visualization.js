const d3 = require('d3')
d3.select(svg).selectAll("*").remove();

function fillPieces(row, col, color, offset) {
    if (color == "red") // Red L-Piece
        d3.select(svg)
            .append("rect")
            .style("fill", "red")
            .attr("x", 5+(row*25))
            .attr("y", 5+(col*25)+offset*120)
            .attr('width', 25)
            .attr('height', 25)
    if (color == "blue") // Blue L-Piece
        d3.select(svg)
            .append("rect")
            .style("fill", "blue")
            .attr("x", 5+(row*25))
            .attr("y", 5+(col*25)+offset*120)
            .attr('width', 25)
            .attr('height', 25)
    if (color == "neutral") // Neutral 
         d3.select(svg)
            .append("rect")
            .style("fill", "gray")
            .attr("x", 5+(row*25))
            .attr("y", 5+(col*25)+offset*120)
            .attr('width', 25)
            .attr('height', 25)
}   

function printState(offset) {
  drawGrid(offset)
  // Iterate through pieces in Game (red, blue, neutral) and call fillPieces
  const red = instances[offset].field("red").tuples()
  const blue = instances[offset].field("blue").tuples()
  const neutral = instances[offset].field("neutral").tuples()


  for (i=0; i<4; i++){
    fillPieces(parseInt(red[i].atoms(0)[1].id()) + 2, parseInt(red[i].atoms(0)[2].id()) + 2, "red", offset)
    // not letting me fill blue in the loop for some reason
  }

  fillPieces(parseInt(blue[0].atoms(0)[1].id()) + 2, parseInt(blue[0].atoms(0)[2].id()) + 2, "blue", offset)
  fillPieces(parseInt(blue[1].atoms(0)[1].id()) + 2, parseInt(blue[1].atoms(0)[2].id()) + 2, "blue", offset)
  fillPieces(parseInt(blue[2].atoms(0)[1].id()) + 2, parseInt(blue[2].atoms(0)[2].id()) + 2, "blue", offset)
  fillPieces(parseInt(blue[3].atoms(0)[1].id()) + 2, parseInt(blue[3].atoms(0)[2].id()) + 2, "blue", offset)

  for (i=0; i<2; i++) {
    fillPieces(parseInt(neutral[i].atoms(0)[1].id()) + 2, parseInt(neutral[i].atoms(0)[2].id()) + 2, "neutral", offset)
  }
  
}

function drawGrid(offset) {
  d3.select(svg)
    .append('rect')
    .attr('x', 5)
    .attr('y', 5+offset*120)
    .attr('width', 100)
    .attr('height', 100)
    .attr('stroke-width', 2)
    .attr('stroke', 'black')
    .attr('fill', 'transparent');
  for(i = 1; i < 4; i++)
    d3.select(svg)
      .append('line')
      .style("stroke", "black")
      .style("stroke-width", 3)
      .attr("x1", 5)
      .attr("y1", 5 + 25*i + offset*120)
      .attr("x2", 105)
      .attr("y2", 5 + 25*i + offset*120); 
  for(i = 1; i < 4; i++)
    d3.select(svg)
      .append('line')
      .style("stroke", "black")
      .style("stroke-width", 3)
      .attr("x1", 5 + 25*i)
      .attr("y1", 5 + offset*120)
      .attr("x2", 5 + 25*i)
      .attr("y2", 105 + offset*120); 
}

printState(0)
printState(1)
printState(2)
